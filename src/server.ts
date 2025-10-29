#!/usr/bin/env node
import { spawn } from "node:child_process";
import { readFile } from "node:fs/promises";
import { z } from "zod";
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";

// ============================================================================
// Types
// ============================================================================

type Scope = {
  workspace?: string;
  group?: string;
  environment?: string;
};

type RadRunOptions = {
  scope?: Scope;
  expectJson?: boolean;
  background?: boolean;
  context?: string;
  json?: boolean;
};

type RadRunResult = {
  code: number;
  stdout: string;
  stderr: string;
};

// ============================================================================
// Scope Helpers
// ============================================================================

function buildScopeArgs(scope?: Scope): string[] {
  if (!scope) return [];
  const args: string[] = [];
  if (scope.workspace) args.push("--workspace", scope.workspace);
  return args;
}

function describeMissingScope(scope: Scope | undefined, requiredKeys: Array<keyof Scope>): string | undefined {
  const missing = requiredKeys.filter((key) => !scope?.[key]);
  if (!missing.length) return undefined;
  const humanList = missing.map((key) => `scope.${key}`).join(", ");
  return `Provide ${humanList} to continue.`;
}

// ============================================================================
// CLI Wrapper
// ============================================================================

class RadCli {
  constructor(private readonly binary = "rad") {}

  async run(subcommand: string[], options: RadRunOptions = {}): Promise<RadRunResult> {
    const { scope, expectJson, background, json } = options;
    const wantsJson = json ?? expectJson ?? false;
    const args = [...subcommand, ...buildScopeArgs(scope)];
    if (wantsJson) {
      args.push("-o", "json");
    }

    return new Promise<RadRunResult>((resolve, reject) => {
      const child = spawn(this.binary, args, {
        stdio: ["ignore", "pipe", "pipe"],
        detached: Boolean(background),
      });

      let stdout = "";
      let stderr = "";

      child.stdout?.on("data", (chunk) => {
        stdout += String(chunk);
      });

      child.stderr?.on("data", (chunk) => {
        stderr += String(chunk);
      });

      child.on("error", (err: NodeJS.ErrnoException) => {
        if (err.code === "ENOENT") {
          reject(new Error("The 'rad' CLI executable was not found on PATH. Install the Radius CLI first."));
        } else {
          reject(err);
        }
      });

      if (background) {
        child.unref();
        setTimeout(() => {
          resolve({
            code: 0,
            stdout: `Background process started with PID ${child.pid}`,
            stderr: "",
          });
        }, 500);
        return;
      }

      child.on("close", (code) => {
        resolve({ code: code ?? 0, stdout, stderr });
      });
    });
  }

  async runJson<T>(subcommand: string[], options: Omit<RadRunOptions, "expectJson"> = {}): Promise<T> {
    const result = await this.run(subcommand, { ...options, expectJson: true });
    if (result.code !== 0) {
      throw handleRadError(result.code, result.stderr, result.stdout, options.context ?? subcommand.join(" "));
    }
    const jsonPayload = extractJsonPayload(result.stdout);
    if (!jsonPayload) {
      return [] as unknown as T;
    }
    try {
      return JSON.parse(jsonPayload) as T;
    } catch (err) {
      throw new Error(`Failed to parse JSON from rad ${subcommand.join(" ")}: ${(err as Error).message}`);
    }
  }
}

// ============================================================================
// Parameter Collection
// ============================================================================

type ParameterCollection = {
  names: Set<string>;
  diagnostics: string[];
};

class ParameterCollector {
  static async collect(parameterFiles?: string[]): Promise<ParameterCollection> {
    const names = new Set<string>();
    const diagnostics: string[] = [];
    if (!parameterFiles?.length) {
      return { names, diagnostics };
    }

    for (const file of parameterFiles) {
      try {
        if (file.endsWith(".json") || file.endsWith(".jsonc")) {
          this.collectFromJson(await readFile(file, "utf8"), names, diagnostics, file);
        } else if (file.endsWith(".bicepparam")) {
          this.collectFromBicepParam(await readFile(file, "utf8"), names, diagnostics, file);
        } else {
          diagnostics.push(`Unsupported parameter file format for ${file}. Provide .json or .bicepparam files.`);
        }
      } catch (err) {
        diagnostics.push(`Failed to read ${file}: ${(err as Error).message}`);
      }
    }

    return { names, diagnostics };
  }

  private static collectFromJson(
    contents: string,
    names: Set<string>,
    diagnostics: string[],
    file: string
  ) {
    try {
      const data = JSON.parse(contents) as unknown;
      if (data && typeof data === "object" && "parameters" in data && typeof (data as { parameters: unknown }).parameters === "object") {
        for (const key of Object.keys((data as { parameters: Record<string, unknown> }).parameters ?? {})) {
          names.add(key);
        }
      } else {
        diagnostics.push(`No parameters section found in ${file}.`);
      }
    } catch (err) {
      diagnostics.push(`Failed to parse parameters from ${file}: ${(err as Error).message}`);
    }
  }

  private static collectFromBicepParam(
    contents: string,
    names: Set<string>,
    diagnostics: string[],
    file: string
  ) {
    const paramRegex = /^\s*(?:@.+\s+)?param\s+([A-Za-z_][\w]*)\b/;
    const seenInFile = new Set<string>();
    const lines = contents.split(/\r?\n/);
    for (const line of lines) {
      const match = paramRegex.exec(line);
      if (!match) continue;
      const name = match[1];
      if (!seenInFile.has(name)) {
        names.add(name);
        seenInFile.add(name);
      }
    }
    if (!seenInFile.size) {
      diagnostics.push(`No param declarations found in ${file}. Ensure the file contains parameter assignments like 'param name value'.`);
    }
  }
}

// ============================================================================
// Bicep Analysis
// ============================================================================

type BicepAnalysis = {
  requiredParameters: string[];
  optionalParameters: string[];
  diagnostics: string[];
  extensionAliases: string[];
  customResourceTypes: string[];
  customResourceNamespaces: string[];
};

const EXTENSION_REGEX = /^\s*extension\s+([A-Za-z_][\w]*)\b/;
const RESOURCE_REGEX = /^\s*(?:resource|existing)\s+[A-Za-z_][\w]*\s+'([^']+)'/;
const PARAM_DECLARATION_REGEX = /^\s*(?:@.+\s+)?param\s+([A-Za-z_][\w]*)\s+[^=\s]+(?:\s*=\s*(.+))?/;

class BicepAnalyzer {
  static async analyze(file: string): Promise<BicepAnalysis> {
    const diagnostics: string[] = [];
    let contents = "";
    try {
      contents = await readFile(file, "utf8");
    } catch (err) {
      diagnostics.push(`Failed to read ${file}: ${(err as Error).message}`);
      return {
        requiredParameters: [],
        optionalParameters: [],
        diagnostics,
        extensionAliases: [],
        customResourceTypes: [],
        customResourceNamespaces: [],
      };
    }

    const { requiredParameters, optionalParameters, parameterDiagnostics } = this.parseParameters(contents);
    diagnostics.push(...parameterDiagnostics);

    const extensionAliases = new Set<string>();
    const customResourceTypes = new Set<string>();
    const customResourceNamespaces = new Set<string>();

    for (const line of contents.split(/\r?\n/)) {
      const extMatch = EXTENSION_REGEX.exec(line);
      if (extMatch) {
        extensionAliases.add(extMatch[1]);
        continue;
      }

      const resourceMatch = RESOURCE_REGEX.exec(line);
      if (resourceMatch) {
        const resourceType = resourceMatch[1];
        const namespace = extractNamespaceFromResourceType(resourceType);
        if (namespaceRequiresExtension(namespace)) {
          customResourceTypes.add(resourceType);
          customResourceNamespaces.add(namespace);
        }
      }
    }

    const customNamespaces = Array.from(customResourceNamespaces);
    const missingExtension = customNamespaces.length > 0 && extensionAliases.size === 0;

    if (missingExtension) {
      diagnostics.push(
        "BCP081: Custom provider resource types detected but no extension declaration found. Add an extension near the top of the file (e.g. 'extension myExtension') that matches the provider namespace configured in bicepconfig.json."
      );
    } else if (customResourceTypes.size) {
      diagnostics.push(
        "Custom provider resource types detected. Validate their schemas against the provider documentation or CLI output."
      );
    }

    if (!requiredParameters.length && !optionalParameters.length) {
      diagnostics.push("No param declarations found via fallback parsing.");
    }

    return {
      requiredParameters,
      optionalParameters,
      diagnostics,
      extensionAliases: Array.from(extensionAliases),
      customResourceTypes: Array.from(customResourceTypes),
      customResourceNamespaces: customNamespaces,
    };
  }

  private static parseParameters(contents: string) {
    const requiredParameters: string[] = [];
    const optionalParameters: string[] = [];
    const diagnostics: string[] = [];
    const seen = new Set<string>();

    for (const line of contents.split(/\r?\n/)) {
      const match = PARAM_DECLARATION_REGEX.exec(line);
      if (!match) continue;
      const name = match[1];
      if (seen.has(name)) continue;
      seen.add(name);
      if (match[2] !== undefined) {
        optionalParameters.push(name);
      } else {
        requiredParameters.push(name);
      }
    }

    return { requiredParameters, optionalParameters, parameterDiagnostics: diagnostics };
  }
}

// ============================================================================
// Namespace Helpers
// ============================================================================

const BUILT_IN_NAMESPACE_PREFIXES = ["Applications.", "Microsoft."];

function normalizeNamespace(value: string): string {
  const withoutVersion = value.split("@")[0] ?? value;
  const beforeSlash = withoutVersion.split("/")[0] ?? withoutVersion;
  return beforeSlash.trim();
}

function isBuiltInNamespace(value: string): boolean {
  const normalized = normalizeNamespace(value);
  return BUILT_IN_NAMESPACE_PREFIXES.some((prefix) => normalized.startsWith(prefix));
}

function extractNamespaceFromItem(item: Record<string, unknown>): string {
  const preferredKeys = [
    "namespace",
    "name",
    "type",
    "resourcetype",
    "resourceprovidername",
    "resourceprovidernamespace",
    "fullname",
    "fullyqualifiedname",
    "id",
  ];

  for (const [rawKey, rawValue] of Object.entries(item)) {
    if (typeof rawValue !== "string" || !rawValue.trim()) continue;
    if (!preferredKeys.includes(rawKey.toLowerCase())) continue;
    return normalizeNamespace(rawValue.trim());
  }
  return "";
}

function deriveNamespaceFromItem(item: unknown): string {
  if (typeof item === "string") {
    return normalizeNamespace(item);
  }
  if (item && typeof item === "object") {
    return extractNamespaceFromItem(item as Record<string, unknown>);
  }
  return "";
}

function extractNamespaceFromResourceType(resourceType: string): string {
  const [withoutVersion] = resourceType.split("@", 1);
  const typePart = withoutVersion ?? resourceType;
  const slashIndex = typePart.indexOf("/");
  return slashIndex >= 0 ? typePart.slice(0, slashIndex) : typePart;
}

function namespaceRequiresExtension(namespace: string): boolean {
  if (!namespace) return false;
  return !namespace.startsWith("Microsoft.");
}

function parseResourceTypeIdentifier(identifier: string): { baseType: string; version?: string } {
  const trimmed = identifier.trim();
  if (!trimmed) {
    return { baseType: "" };
  }
  const atIndex = trimmed.lastIndexOf("@");
  if (atIndex > trimmed.indexOf("/") && atIndex > 0 && atIndex < trimmed.length - 1) {
    const baseType = trimmed.slice(0, atIndex);
    const version = trimmed.slice(atIndex + 1);
    return { baseType, version };
  }
  return { baseType: trimmed };
}

// ============================================================================
// Error Handling
// ============================================================================

function handleRadError(code: number, stderr: string, stdout: string, context: string): Error {
  const errorOutput = stderr || stdout || `rad command failed with exit code ${code}`;
  if (errorOutput.includes("workspace") || errorOutput.includes("context")) {
    return new Error(`${context} failed: ${errorOutput}\nSuggestion: Run workspace-switch or workspace-create_kubernetes first.`);
  }
  if (errorOutput.includes("group") || errorOutput.includes("resource group")) {
    return new Error(`${context} failed: ${errorOutput}\nSuggestion: Run group-create or group-switch first.`);
  }
  if (errorOutput.includes("environment")) {
    return new Error(`${context} failed: ${errorOutput}\nSuggestion: Run env-create or env-switch first.`);
  }
  return new Error(`${context} failed (exit code ${code}): ${errorOutput}`);
}

// ============================================================================
// Response Helpers
// ============================================================================

type ToolResponse = {
  content: Array<{ type: "text"; text: string }>;
  structuredContent?: Record<string, unknown>;
};

function formatTextPayload(payload: unknown): string {
  if (payload === null || payload === undefined) {
    return "null";
  }
  if (typeof payload === "string") {
    return payload;
  }
  return JSON.stringify(payload, null, 2);
}

function respond(payload: unknown, structuredContent?: Record<string, unknown>): ToolResponse {
  return {
    content: [{ type: "text", text: formatTextPayload(payload) }],
    structuredContent,
  };
}

function extractJsonPayload(rawOutput: string): string | undefined {
  const trimmed = stripAnsi(rawOutput).trim();
  if (!trimmed) return undefined;
  if (trimmed.startsWith("{") || trimmed.startsWith("[")) {
    return trimTrailingNonJson(trimmed);
  }
  const lines = trimmed.split(/\r?\n/);
  const startIndex = lines.findIndex((line) => {
    const l = line.trimStart();
    return l.startsWith("{") || l.startsWith("[");
  });
  if (startIndex === -1) return undefined;
  const candidate = lines.slice(startIndex).join("\n").trimStart();
  if (!candidate) return undefined;
  return trimTrailingNonJson(candidate.trim());
}

function trimTrailingNonJson(candidate: string): string {
  const lastCurly = candidate.lastIndexOf("}");
  const lastSquare = candidate.lastIndexOf("]");
  const endIndex = Math.max(lastCurly, lastSquare);
  if (endIndex === -1) {
    return candidate;
  }
  return candidate.slice(0, endIndex + 1);
}

function stripAnsi(value: string): string {
  return value.replace(/\u001b\[[0-9;]*[A-Za-z]/g, "");
}

// ============================================================================
// MCP Server Setup
// ============================================================================

const mcp = new McpServer({ name: "radius-mcp", version: "0.3.0" });
const rad = new RadCli();

const ScopeSchema = z
  .object({
    workspace: z.string().optional().describe("Workspace name"),
    group: z.string().optional().describe("Resource group name"),
    environment: z.string().optional().describe("Environment name"),
  })
  .optional();

async function resolveScopeDefaults(scope: Scope | undefined): Promise<{ scope: Scope | undefined; diagnostics: string[] }> {
  const diagnostics: string[] = [];
  if (!scope) {
    return { scope: undefined, diagnostics };
  }

  const resolvedScope: Scope = { ...scope };
  const hasEnvironment = Boolean(resolvedScope.environment);
  const hasGroup = Boolean(resolvedScope.group);

  if (hasEnvironment && !hasGroup) {
    const environmentName = resolvedScope.environment as string;
    try {
      const envDetails = await rad.runJson<unknown>(["environment", "show", environmentName], {
        scope: resolvedScope.workspace ? { workspace: resolvedScope.workspace } : undefined,
        context: "resolve-scope",
      });
      const discoveredGroup = extractResourceGroupFromEnvironmentInfo(envDetails);
      if (discoveredGroup) {
        resolvedScope.group = discoveredGroup;
        diagnostics.push(`Scope: Using resource group '${discoveredGroup}' from environment '${environmentName}'.`);
      } else {
        diagnostics.push(
          `Scope: Unable to determine the resource group for environment '${environmentName}'. Provide scope.group explicitly.`
        );
      }
    } catch (err) {
      diagnostics.push(
        `Scope: Failed to retrieve environment details for '${environmentName}': ${(err as Error).message}`
      );
    }
  }

  return { scope: resolvedScope, diagnostics };
}

function extractResourceGroupFromEnvironmentInfo(info: unknown): string | undefined {
  if (!info || typeof info !== "object") return undefined;
  const record = info as Record<string, unknown>;
  const candidateKeys = ["resourceGroup", "group", "resource_group", "resourcegroup"];

  for (const key of candidateKeys) {
    const value = record[key];
    if (typeof value === "string" && value.trim()) {
      return value.trim();
    }
  }

  const properties = record.properties;
  if (properties && typeof properties === "object") {
    const propsRecord = properties as Record<string, unknown>;
    for (const key of candidateKeys) {
      const value = propsRecord[key];
      if (typeof value === "string" && value.trim()) {
        return value.trim();
      }
    }
  }

  return undefined;
}

// ============================================================================
// Resource Catalog Tool
// ============================================================================

mcp.registerTool(
  "list_resource_types",
  {
    title: "List Radius Resource Types",
    description:
      "List available Radius resource types, excluding built-in namespaces so new provider namespaces are highlighted.",
    inputSchema: {
      scope: ScopeSchema,
      excludeNamespaces: z.array(z.string()).optional().describe("Additional namespace prefixes to filter out"),
    },
    outputSchema: {
      resourceTypes: z.array(z.any()),
    },
  },
  async ({ scope, excludeNamespaces }) => {
    const scopeForCommand = scope?.workspace ? { workspace: scope.workspace } : undefined;

    const rawItems = await rad.runJson<unknown[]>(["resource-type", "list"], {
      scope: scopeForCommand,
      context: "list_resource_types",
    });

    const filters = [...(excludeNamespaces ?? [])];

    const filtered = (Array.isArray(rawItems) ? rawItems : []).filter((item) => {
      const namespace = deriveNamespaceFromItem(item);
      if (namespace && isBuiltInNamespace(namespace)) {
        return false;
      }
      if (!filters.length) return true;
      return !filters.some((prefix) => namespace.startsWith(prefix));
    });

    const display = filtered.length
      ? filtered
      : "No resource types matched the current filters. Try adjusting excludeNamespaces.";

    return respond(display, { resourceTypes: filtered });
  }
);

// ============================================================================
// Authoring Tools
// ============================================================================

mcp.registerTool(
  "pre-edit-bicep",
  {
    title: "Pre-Edit Bicep Guidance",
    description: "Run before editing Bicep files for best practices and guardrails.",
    inputSchema: {
      file: z.string().optional().describe("Path to the Bicep file you plan to modify"),
      scope: ScopeSchema,
    },
    outputSchema: {
      checklist: z.array(z.string()),
      reminders: z.array(z.string()),
    },
  },
  async ({ file, scope }) => {
    const checklist = [
      "Confirm you are targeting the intended Radius workspace, group, and environment.",
      "Identify the provider namespace and latest API version for any new resource types you intend to add.",
      "Run the resource-type-show tool for each resource type you plan to add to inspect its schema and required parameters.",
      "Open bicepconfig.json and map each provider namespace to the configured extension alias before declaring new resources.",
      "Ensure the required extension declaration from bicepconfig.json is present at the top of the file before adding new resources.",
    ];

    const reminders: string[] = [];
    const scopeArgs = buildScopeArgs(scope ?? undefined);
    if (scopeArgs.length) {
      reminders.push(`Scope context: ${scopeArgs.join(" ")}`);
    }

    if (file) {
      reminders.push(`Planned file: ${file}`);
      const analysis = await BicepAnalyzer.analyze(file);
      reminders.push(`Detected parameters: required(${analysis.requiredParameters.length}), optional(${analysis.optionalParameters.length})`);
      if (analysis.customResourceNamespaces.length) {
        reminders.push(
          `Custom resource namespaces: ${analysis.customResourceNamespaces.join(
            ", "
          )}. Run resource-type-show to review the schema, then verify the matching extension alias is defined in bicepconfig.json.`
        );
        reminders.push("Before adding new resources, open bicepconfig.json and confirm which extension alias maps to each namespace.");
      }
      if (analysis.customResourceTypes.length) {
        const baseTypes = Array.from(
          new Set(
            analysis.customResourceTypes
              .map((resourceType) => parseResourceTypeIdentifier(resourceType).baseType)
              .filter((value): value is string => Boolean(value))
          )
        );
        if (baseTypes.length) {
          reminders.push(
            `Schema lookup: Run resource-type-show for ${baseTypes.join(", ")} to inspect required properties before editing.`
          );
        }
      }
      for (const diagnostic of analysis.diagnostics) {
        reminders.push(`Insight: ${diagnostic}`);
      }
      if (!analysis.extensionAliases.length && analysis.customResourceNamespaces.length) {
        reminders.push(
          "Action: Add an extension declaration (e.g. `extension myExtension`) that aligns with the provider namespace from bicepconfig.json."
        );
      }
    } else {
      reminders.push("Provide a Bicep file path for targeted guidance.");
      reminders.push("If you plan to add a new resource, open bicepconfig.json now to locate the extension alias for its provider namespace.");
      reminders.push("Before editing, run resource-type-show for the resource type you intend to add to understand its schema.");
    }

    return respond({ checklist, reminders }, { checklist, reminders });
  }
);

mcp.registerTool(
  "post-edit-bicep",
  {
    title: "Validate Bicep Changes",
    description: "Run after edits to confirm Radius extensions, review diagnostics, and capture next steps before deployment.",
    inputSchema: {
      file: z.string().describe("Path to the Bicep file that was just edited"),
      scope: ScopeSchema,
    },
    outputSchema: {
      status: z.enum(["pass", "warn", "fail"]),
      extensionAliases: z.array(z.string()),
      customResourceTypes: z.array(z.string()),
      customResourceNamespaces: z.array(z.string()),
      requiredParameters: z.array(z.string()),
      optionalParameters: z.array(z.string()),
      blockingIssues: z.array(z.string()),
      warnings: z.array(z.string()),
      nextSteps: z.array(z.string()),
    },
  },
  async ({ file, scope }) => {
    const analysis = await BicepAnalyzer.analyze(file);
    const blockingIssues: string[] = [];
    const warnings: string[] = [];
    const nextSteps: string[] = [];

    if (scope) {
      const scopeArgs = buildScopeArgs(scope);
      if (scopeArgs.length) {
        nextSteps.push(`Scope context: ${scopeArgs.join(" ")}`);
      }
    }

    for (const diagnostic of analysis.diagnostics) {
      if (diagnostic.startsWith("BCP081")) {
        blockingIssues.push(diagnostic);
      } else {
        warnings.push(diagnostic);
      }
    }

    if (analysis.customResourceTypes.length && !analysis.extensionAliases.length) {
      blockingIssues.push(
        "Custom provider resource types are defined but no extension declaration was found. Add an extension at the top of the file that maps to the provider namespace configured in bicepconfig.json."
      );
    }

    if (analysis.customResourceTypes.length) {
      nextSteps.push("Re-run pre-deploy-checks to confirm parameters and extension compliance.");
    } else {
      nextSteps.push("Verify resource dependencies and outputs align with expected consumers.");
    }

    if (!analysis.requiredParameters.length) {
      warnings.push("No required parameters detected. Confirm that defaults are intentional.");
    }

    const status = blockingIssues.length ? "fail" : warnings.length ? "warn" : "pass";

    const structured = {
      status,
      extensionAliases: analysis.extensionAliases,
      customResourceTypes: analysis.customResourceTypes,
      customResourceNamespaces: analysis.customResourceNamespaces,
      requiredParameters: analysis.requiredParameters,
      optionalParameters: analysis.optionalParameters,
      blockingIssues,
      warnings,
      nextSteps,
    };

    return respond(structured, structured);
  }
);

// ============================================================================
// Application Tools
// ============================================================================

mcp.registerTool(
  "app-graph",
  {
    title: "Show Application Graph",
    description: "Show application resources and relationships.",
    inputSchema: {
      name: z.string().optional().describe("Application name (defaults to scope.application)"),
      scope: ScopeSchema,
    },
    outputSchema: {
      graph: z.any(),
    },
  },
  async ({ name, scope }) => {
    const scopeForCommand = scope ? { ...scope } : undefined;
    if (scopeForCommand) {
      delete scopeForCommand.environment;
    }
    const args = ["application", "graph"];
    if (name) args.push(name);

    const result = await rad.run(args, {
      scope: scopeForCommand,
      context: "app-graph",
      json: false,
    });
    if (result.code !== 0) {
      throw handleRadError(result.code, result.stderr, result.stdout, "app-graph");
    }

    const parsedGraph = parseApplicationGraph(result.stdout);
    const summary = summarizeParsedApplicationGraph(parsedGraph);
    return respond(summary, { graph: parsedGraph });
  }
);

type ParsedApplicationNode = {
  name: string;
  type: string;
  connections: string[];
  resources: string[];
};

type ParsedApplicationGraph = {
  application?: string;
  nodes: ParsedApplicationNode[];
};

function parseApplicationGraph(output: string): ParsedApplicationGraph {
  const nodes: ParsedApplicationNode[] = [];
  const lines = stripAnsi(output).split(/\r?\n/);
  let current: ParsedApplicationNode | undefined;
  let currentSection: "connections" | "resources" | undefined;
  let applicationName: string | undefined;

  for (const rawLine of lines) {
    const line = rawLine.trimEnd();
    const trimmed = line.trim();
    if (!trimmed) continue;

    if (trimmed.startsWith("Displaying application:")) {
      applicationName = trimmed.replace("Displaying application:", "").trim();
      continue;
    }

    if (trimmed.startsWith("Name: ")) {
      if (current) {
        nodes.push(current);
      }
      const nameSection = trimmed.slice("Name: ".length);
      const nameMatch = nameSection.match(/^(.*?)\s+\((.+)\)$/);
      const name = nameMatch ? nameMatch[1] : nameSection;
      const type = nameMatch ? nameMatch[2] : "";
      current = { name, type, connections: [], resources: [] };
      currentSection = undefined;
      continue;
    }

    if (trimmed.startsWith("Connections:")) {
      currentSection = trimmed.includes("(none)") ? undefined : "connections";
      continue;
    }

    if (trimmed.startsWith("Resources:")) {
      currentSection = trimmed.includes("(none)") ? undefined : "resources";
      continue;
    }

    if (rawLine.startsWith("  ") && current) {
      if (currentSection === "connections") {
        current.connections.push(trimmed);
      } else if (currentSection === "resources") {
        current.resources.push(trimmed);
      }
    }
  }

  if (current) {
    nodes.push(current);
  }

  return { application: applicationName, nodes };
}

function summarizeParsedApplicationGraph(graph: ParsedApplicationGraph): string {
  if (!graph.nodes.length) {
    return graph.application
      ? `No resources found for application '${graph.application}'.`
      : "No resources found for this application.";
  }

  const parts: string[] = [];
  if (graph.application) {
    parts.push(`Application: ${graph.application}`);
  }
  const totalNodes = graph.nodes.length;
  const totalConnections = graph.nodes.reduce((count, node) => count + node.connections.length, 0);
  const totalResources = graph.nodes.reduce((count, node) => count + node.resources.length, 0);
  parts.push(`Components: ${totalNodes}, Connections: ${totalConnections}, Underlying resources: ${totalResources}`);

  const highlights = graph.nodes.slice(0, 3).map((node) => {
    const connections = node.connections.length ? `${node.connections.length} link(s)` : "no links";
    const resources = node.resources.length ? `${node.resources.length} resource(s)` : "no backing resources";
    return `- ${node.name} (${node.type || "type unknown"}): ${connections}, ${resources}`;
  });

  parts.push(...highlights);
  if (graph.nodes.length > 3) {
    parts.push(`(+${graph.nodes.length - 3} more components in structured output)`);
  }

  parts.push("See structured content for the parsed graph.");
  return parts.join("\n");
}

// ============================================================================
// Resource Metadata Tools
// ============================================================================

mcp.registerTool(
  "resource-type-show",
  {
    title: "Show Resource Type Schema",
    description: "Retrieve the schema/definition for a specific Radius resource type.",
    inputSchema: {
      type: z.string().describe("Fully qualified resource type identifier (e.g. My.ResourceNamespace/resource@2023-10-01-preview)"),
      scope: ScopeSchema,
      raw: z
        .boolean()
        .optional()
        .describe("Set to true to return the raw JSON payload without additional summarization."),
    },
    outputSchema: {
      resourceType: z.any(),
    },
  },
  async ({ type, scope, raw }) => {
    const identifier = type.trim();
    if (!identifier) {
      throw new Error("resource-type-show requires a non-empty resource type identifier.");
    }

    const { baseType, version } = parseResourceTypeIdentifier(identifier);
    const scopeForCommand = scope?.workspace ? { workspace: scope.workspace } : undefined;
    const result = await rad.run(["resource-type", "show", baseType], {
      scope: scopeForCommand,
      context: "resource-type-show",
      expectJson: true,
    });
    if (result.code !== 0) {
      throw handleRadError(result.code, result.stderr, result.stdout, "resource-type-show");
    }

    const jsonPayload = extractJsonPayload(result.stdout);
    if (!jsonPayload) {
      throw new Error(`resource-type-show failed: No JSON output returned for ${identifier}.`);
    }

    let parsed: unknown;
    try {
      parsed = JSON.parse(jsonPayload) as unknown;
    } catch (err) {
      throw new Error(`resource-type-show failed to parse JSON: ${(err as Error).message}`);
    }

    const structured: Record<string, unknown> = {
      resourceType: parsed,
      request: {
        identifier,
        baseType,
        version,
      },
    };

    if (raw) {
      return respond(parsed, structured);
    }

    const summary = summarizeResourceType(parsed, baseType, version);
    return respond(summary, structured);
  }
);

function summarizeResourceType(payload: unknown, typeName: string, requestedVersion?: string): string {
  if (!payload || typeof payload !== "object") {
    return `Resource type ${typeName} retrieved. See structured content for full details.`;
  }

  const record = payload as Record<string, unknown>;
  const provider =
    typeof record.ResourceProviderNamespace === "string"
      ? record.ResourceProviderNamespace
      : typeof record.resourceProviderNamespace === "string"
        ? record.resourceProviderNamespace
        : undefined;

  const apiVersions = extractApiVersionMap(record);
  const versionList = apiVersions ? Object.keys(apiVersions) : [];
  const chosenVersion = requestedVersion ?? versionList[0];
  const versionDetails =
    chosenVersion && apiVersions && Object.prototype.hasOwnProperty.call(apiVersions, chosenVersion)
      ? (apiVersions[chosenVersion] as Record<string, unknown>)
      : undefined;

  const lines: string[] = [`Type: ${typeName}`];
  if (provider) {
    lines.push(`Provider: ${provider}`);
  }
  lines.push(`API versions: ${versionList.length ? versionList.join(", ") : "unknown"}`);
  if (requestedVersion && !versionDetails) {
    lines.push(`Requested version '${requestedVersion}' not found in CLI output. See structured content for available versions.`);
  }

  const schemaNode = versionDetails
    ? (versionDetails.Schema ?? versionDetails.schema ?? versionDetails) ?? undefined
    : undefined;
  const propertyCount = countSchemaPropertiesFromSchema(schemaNode);
  if (typeof propertyCount === "number") {
    lines.push(`Top-level properties: ${propertyCount}`);
  }

  const requiredParameters = extractCollection(
    versionDetails?.RequiredParameters ?? versionDetails?.requiredParameters ?? record.RequiredParameters ?? record.requiredParameters
  );
  if (requiredParameters.length) {
    lines.push(`Required parameters: ${requiredParameters.join(", ")}`);
  }

  lines.push("See structured content for complete schema details.");
  return lines.join("\n");
}

function extractCollection(value: unknown): string[] {
  if (!value) return [];
  if (Array.isArray(value)) {
    return value
      .map((item) => (typeof item === "string" ? item : ""))
      .filter((item): item is string => Boolean(item?.trim()))
      .map((item) => item.trim());
  }
  if (typeof value === "string") {
    return [value.trim()];
  }
  return [];
}

function extractApiVersionMap(record: Record<string, unknown>): Record<string, unknown> | undefined {
  const apiVersions = (record.APIVersions ?? record.apiVersions) as unknown;
  if (apiVersions && typeof apiVersions === "object") {
    return apiVersions as Record<string, unknown>;
  }
  return undefined;
}

function countSchemaPropertiesFromSchema(schema: unknown): number | undefined {
  if (!schema || typeof schema !== "object") return undefined;
  const record = schema as Record<string, unknown>;
  const properties = record.properties;
  if (!properties || typeof properties !== "object") return undefined;
  return Object.keys(properties as Record<string, unknown>).length;
}

// ============================================================================
// Resource Group Tools
// ============================================================================

mcp.registerTool(
  "group-list",
  {
    title: "List Resource Groups",
    description: "List Radius resource groups within the active or specified workspace.",
    inputSchema: {
      scope: ScopeSchema,
    },
    outputSchema: {
      groups: z.array(z.any()),
      diagnostics: z.array(z.string()).optional(),
    },
  },
  async ({ scope }) => {
    const { scope: resolvedScope, diagnostics } = await resolveScopeDefaults(scope ?? undefined);
    const scopeForCommand = resolvedScope?.workspace ? { workspace: resolvedScope.workspace } : undefined;

    const groups = await rad.runJson<unknown[]>(["group", "list"], {
      scope: scopeForCommand,
      context: "group-list",
    });

    const structured: Record<string, unknown> = { groups };
    if (diagnostics.length) {
      structured.diagnostics = diagnostics;
    }

    return respond(structured, structured);
  }
);

// ============================================================================
// Environment Tools
// ============================================================================

mcp.registerTool(
  "env-list",
  {
    title: "List Environments",
    description: "List all environments.",
    inputSchema: {
      scope: ScopeSchema,
    },
    outputSchema: {
      environments: z.array(z.any()),
    },
  },
  async ({ scope }) => {
    const environments = await rad.runJson<unknown[]>(["environment", "list"], {
      scope,
      context: "env-list",
    });
    return respond(environments, { environments });
  }
);

mcp.registerTool(
  "env-show",
  {
    title: "Show Environment",
    description: "Show environment details.",
    inputSchema: {
      name: z.string().optional().describe("Environment name (defaults to current)"),
      scope: ScopeSchema,
    },
    outputSchema: {
      environment: z.any(),
    },
  },
  async ({ name, scope }) => {
    const args = ["environment", "show"];
    if (name) args.push(name);
    const environment = await rad.runJson<unknown>(args, {
      scope,
      context: "env-show",
    });
    return respond(environment, { environment });
  }
);

// ============================================================================
// Deploy & Run Tools
// ============================================================================

mcp.registerTool(
  "deploy-template",
  {
    title: "Deploy Template",
    description: "Deploy a Radius/Bicep template with parameters.",
    inputSchema: {
      file: z.string().describe("Path to deployment template (.bicep file)"),
      parameters: z.record(z.union([z.string(), z.number(), z.boolean()])).optional().describe("Parameters as key-value pairs"),
      parameterFiles: z.array(z.string()).optional().describe("Paths to parameter files (.json or .bicepparam)"),
      scope: ScopeSchema,
    },
    outputSchema: {
      output: z.string(),
      success: z.boolean(),
    },
  },
  async ({ file, parameters, parameterFiles, scope }) => {
    const { scope: resolvedScope, diagnostics: scopeDiagnostics } = await resolveScopeDefaults(scope ?? undefined);
    const scopeError = describeMissingScope(resolvedScope, ["environment"]);
    if (scopeError) {
      const messageParts = [
        "deploy-template requires target environment.",
        scopeError,
        ...scopeDiagnostics,
      ].filter(Boolean);
      throw new Error(messageParts.join("\n"));
    }

    const args = ["deploy", file, ...buildParameterArgs(parameters, parameterFiles)];
    const result = await rad.run(args, { scope: resolvedScope, context: "deploy-template" });
    if (result.code !== 0) {
      throw handleRadError(result.code, result.stderr, result.stdout, "deploy-template");
    }
    const structured: Record<string, unknown> = {
      output: result.stdout,
      success: true,
    };
    if (resolvedScope) {
      structured.scope = resolvedScope;
    }
    if (scopeDiagnostics.length) {
      structured.notes = scopeDiagnostics;
    }
    const textPayload =
      scopeDiagnostics.length && scopeDiagnostics[0]
        ? `${result.stdout || "Deployment completed."}\n${scopeDiagnostics.join("\n")}`
        : result.stdout || "Deployment completed.";
    return respond(textPayload, structured);
  }
);

mcp.registerTool(
  "pre-deploy-checks",
  {
    title: "Pre-Deploy Checks",
    description: "Inspect a Bicep template, enforce required Radius extensions, and highlight required parameters.",
    inputSchema: {
      file: z.string().describe("Path to deployment template (.bicep file)"),
      parameters: z
        .record(z.union([z.string(), z.number(), z.boolean()]))
        .optional()
        .describe("Parameters currently planned for deployment"),
      parameterFiles: z.array(z.string()).optional().describe("Paths to parameter files (.json or .bicepparam)"),
      scope: ScopeSchema,
    },
    outputSchema: {
      requiredParameters: z.array(z.string()),
      optionalParameters: z.array(z.string()),
      missingParameters: z.array(z.string()),
      providedParameters: z.array(z.string()),
      extensionAliases: z.array(z.string()),
      customResourceTypes: z.array(z.string()),
      customResourceNamespaces: z.array(z.string()),
      diagnostics: z.array(z.string()),
    },
  },
  async ({ file, parameters, parameterFiles, scope }) => {
    const { scope: resolvedScope, diagnostics: scopeDiagnostics } = await resolveScopeDefaults(scope ?? undefined);
    const analysis = await BicepAnalyzer.analyze(file);
    const provided = new Set<string>(Object.keys(parameters ?? {}));
    const { names: fileParameters, diagnostics: parameterDiagnostics } = await ParameterCollector.collect(parameterFiles);
    fileParameters.forEach((name) => {
      provided.add(name);
    });
    const missingParameters = analysis.requiredParameters.filter((name) => !provided.has(name));
    const diagnostics = [...analysis.diagnostics, ...parameterDiagnostics, ...scopeDiagnostics];

    const scopeError = describeMissingScope(resolvedScope, ["group", "environment"]);
    if (scopeError) {
      diagnostics.push(
        "Scope: Specify the target Radius group and environment (e.g. scope.group, scope.environment) before deploying."
      );
    }

    if (analysis.customResourceTypes.length && !analysis.extensionAliases.length) {
      diagnostics.push(
        "pre-deploy-checks: Custom provider resource types are present but no extension declaration was found. Add an extension (e.g. `extension myExtension`) before deploying."
      );
    }

    const structured: Record<string, unknown> = {
      requiredParameters: analysis.requiredParameters,
      optionalParameters: analysis.optionalParameters,
      providedParameters: Array.from(provided),
      missingParameters,
      extensionAliases: analysis.extensionAliases,
      customResourceTypes: analysis.customResourceTypes,
      customResourceNamespaces: analysis.customResourceNamespaces,
      diagnostics,
    };
    if (resolvedScope) {
      structured.targetScope = resolvedScope;
    }

    return respond(structured, structured);
  }
);

// ============================================================================
// Utility
// ============================================================================

function buildParameterArgs(
  parameters?: Record<string, string | number | boolean>,
  parameterFiles?: string[]
): string[] {
  const args: string[] = [];
  if (parameters) {
    for (const [key, value] of Object.entries(parameters)) {
      args.push("-p", `${key}=${value}`);
    }
  }
  if (parameterFiles) {
    for (const file of parameterFiles) {
      args.push("-p", `@${file}`);
    }
  }
  return args;
}

// ============================================================================
// Start Server
// ============================================================================

async function startServer() {
  const transport = new StdioServerTransport();
  await mcp.connect(transport);
}

void startServer();
