/* eslint-disable security/detect-object-injection, no-inline-comments */
import {
  matchToModulePath,
  matchToModulePathNot,
} from "#validate/matchers.mjs";
import IndexedModuleGraph from "#graph-utl/indexed-module-graph.mjs";
import { extractGroups } from "#utl/regex-util.mjs";

function isReachableRule(pRule) {
  return Object.hasOwn(pRule?.to ?? {}, "reachable");
}

function getReachableRules(pRuleSet) {
  return (pRuleSet?.forbidden ?? [])
    .filter(isReachableRule)
    .concat((pRuleSet?.allowed ?? []).filter(isReachableRule))
    .concat((pRuleSet?.required ?? []).filter(isReachableRule));
}

function isModuleInRuleFrom(pRule) {
  return (pModule) => {
    const lRuleFrom = pRule.from ?? pRule.module;
    if (lRuleFrom) {
      return (
        (!lRuleFrom.path || pModule.source.match(lRuleFrom.path)) &&
        (!lRuleFrom.pathNot || !pModule.source.match(lRuleFrom.pathNot))
      );
    }
    return false;
  };
}

function isModuleInRuleTo(pRule, pModuleTo, pModuleFrom) {
  const lGroups = pModuleFrom
    ? extractGroups(pRule.from ?? pRule.module, pModuleFrom.source)
    : [];

  return (
    matchToModulePath(pRule, pModuleTo, lGroups) &&
    matchToModulePathNot(pRule, pModuleTo, lGroups)
  );
}

function mergeReachableProperties(pModule, pRule, pPath, pModuleFrom) {
  const lReachables = pModule.reachable || [];
  const lIndexExistingReachable = lReachables.findIndex(
    (pReachable) => pReachable.asDefinedInRule === pRule.name,
  );
  const lIsReachable = pPath.length > 0;

  if (lIndexExistingReachable > -1) {
    lReachables[lIndexExistingReachable].value =
      lReachables[lIndexExistingReachable].value || lIsReachable;
    return lReachables;
  }
  return lReachables.concat({
    value: lIsReachable,
    asDefinedInRule: pRule.name,
    matchedFrom: pModuleFrom,
  });
}

function mergeReachesProperties(pFromModule, pToModule, pRule, pPath) {
  const lReaches = pFromModule.reaches || [];
  const lIndexExistingReachable = lReaches.findIndex(
    (pReachable) => pReachable.asDefinedInRule === pRule.name,
  );

  if (lIndexExistingReachable > -1) {
    lReaches[lIndexExistingReachable].modules = (
      lReaches[lIndexExistingReachable].modules /* c8 ignore next */ || []
    ).concat({
      source: pToModule.source,
      via: pPath,
    });
    return lReaches;
  }
  return lReaches.concat({
    asDefinedInRule: pRule.name,
    modules: [{ source: pToModule.source, via: pPath }],
  });
}

function shouldAddReaches(pRule, pModule) {
  return (
    (pRule.to.reachable === true || pRule.name === "not-in-allowed") &&
    isModuleInRuleFrom(pRule)(pModule)
  );
}

function hasCapturingGroups(pRule) {
  const lCapturingGroupPlaceholderRe = /\$[0-9]+/;

  return (
    lCapturingGroupPlaceholderRe.test(pRule?.to?.path ?? "") ||
    lCapturingGroupPlaceholderRe.test(pRule?.to?.pathNot ?? "")
  );
}
function shouldAddReachable(pRule, pModuleTo, pGraph) {
  let lReturnValue = false;

  if (
    pRule.to.reachable === false ||
    pRule.name === "not-in-allowed" ||
    pRule.module
  ) {
    if (hasCapturingGroups(pRule)) {
      const lModulesFrom = pGraph.filter(isModuleInRuleFrom(pRule));

      lReturnValue = lModulesFrom.some((pModuleFrom) =>
        isModuleInRuleTo(pRule, pModuleTo, pModuleFrom),
      );
    } else {
      lReturnValue = isModuleInRuleTo(pRule, pModuleTo);
    }
  }
  return lReturnValue;
}

function addReachesToModule(pModule, pGraph, pIndexedGraph, pReachableRule) {
  const lToModules = pGraph.filter((pToModule) =>
    isModuleInRuleTo(pReachableRule, pToModule, pModule),
  );

  for (let lToModule of lToModules) {
    if (pModule.source !== lToModule.source) {
      const lPath = pIndexedGraph.getPath(pModule.source, lToModule.source);

      if (lPath.length > 0) {
        pModule.reaches = mergeReachesProperties(
          pModule,
          lToModule,
          pReachableRule,
          lPath,
        );
      }
    }
  }
  return pModule;
}

/**
 * Processes dependencies for a single vertex during BFS traversal.
 * Extracted to reduce nesting depth.
 *
 * @param {Object} pVertex - The current vertex
 * @param {Set<string>} pVisited - Set of visited modules
 * @param {Set<string>} pReachableModules - Set of reachable modules
 * @param {Array<string>} pQueue - BFS queue
 */
function processDependencies(pVertex, pVisited, pReachableModules, pQueue) {
  for (let lDependency of pVertex.dependencies) {
    const lDependencyName = lDependency.name || lDependency.resolved;
    if (!pVisited.has(lDependencyName)) {
      pVisited.add(lDependencyName);
      pReachableModules.add(lDependencyName);
      pQueue.push(lDependencyName);
    }
  }
}

/**
 * Calculates all reachable modules from a single source using BFS.
 *
 * @param {string} pSourceModule - Source module to start from
 * @param {IndexedModuleGraph} pIndexedGraph - The indexed graph
 * @returns {Set<string>} Set of reachable modules
 */
function calculateReachableModules(pSourceModule, pIndexedGraph) {
  const lReachableModules = new Set();
  const lQueue = [pSourceModule];
  const lVisited = new Set([pSourceModule]);

  while (lQueue.length > 0) {
    const lCurrentSource = lQueue.shift();
    const lCurrentVertex = pIndexedGraph.findVertexByName(lCurrentSource);

    if (lCurrentVertex) {
      processDependencies(lCurrentVertex, lVisited, lReachableModules, lQueue);
    }
  }

  return lReachableModules;
}

/**
 * Pre-calculates all reachable modules from each "from" module using BFS.
 * This is more efficient than calling getPath for each module individually.
 *
 * @param {Array} pFromModules - Array of modules to calculate reachability from
 * @param {IndexedModuleGraph} pIndexedGraph - The indexed graph
 * @returns {Map<string, Set<string>>} Map from source module to set of reachable modules
 */
function calculateReachabilityMap(pFromModules, pIndexedGraph) {
  const lReachabilityMap = new Map();

  for (let lFromModule of pFromModules) {
    const lReachableModules = calculateReachableModules(
      lFromModule.source,
      pIndexedGraph,
    );
    lReachabilityMap.set(lFromModule.source, lReachableModules);
  }

  return lReachabilityMap;
}

function addReachableToModule(
  pModule,
  pIndexedGraph,
  pReachableRule,
  pContext,
) {
  let lFound = false;

  for (let lFromModule of pContext.fromModules) {
    if (
      !lFound &&
      pModule.source !== lFromModule.source &&
      isModuleInRuleTo(pReachableRule, pModule, lFromModule)
    ) {
      // Use pre-calculated reachability map for fast lookup
      const lReachableModules = pContext.reachabilityMap.get(
        lFromModule.source,
      );
      const lIsReachable =
        lReachableModules && lReachableModules.has(pModule.source);

      if (lIsReachable) {
        // Only call getPath when we know the module is reachable
        const lPath = pIndexedGraph.getPath(lFromModule.source, pModule.source);
        lFound = lPath.length > 0;
        pModule.reachable = mergeReachableProperties(
          pModule,
          pReachableRule,
          lPath,
          lFromModule.source,
        );
      } else {
        // Module is not reachable, set empty path
        pModule.reachable = mergeReachableProperties(
          pModule,
          pReachableRule,
          [],
          lFromModule.source,
        );
      }
    }
  }
  return pModule;
}

function addReachabilityToGraph(pGraph, pIndexedGraph, pReachableRule) {
  const lFromModules = pGraph.filter(isModuleInRuleFrom(pReachableRule));

  // Pre-calculate reachability map for performance optimization
  // This avoids redundant path-finding operations for each module
  const lReachabilityMap = calculateReachabilityMap(
    lFromModules,
    pIndexedGraph,
  );
  const lContext = {
    fromModules: lFromModules,
    reachabilityMap: lReachabilityMap,
  };

  return pGraph.map((pModule) => {
    let lClonedModule = structuredClone(pModule);

    if (shouldAddReaches(pReachableRule, lClonedModule)) {
      lClonedModule = addReachesToModule(
        lClonedModule,
        pGraph,
        pIndexedGraph,
        pReachableRule,
      );
    }
    if (shouldAddReachable(pReachableRule, lClonedModule, pGraph)) {
      lClonedModule = addReachableToModule(
        lClonedModule,
        pIndexedGraph,
        pReachableRule,
        lContext,
      );
    }
    return lClonedModule;
  });
}

export default function deriveReachables(pGraph, pRuleSet) {
  const lReachableRules = pRuleSet ? getReachableRules(pRuleSet) : [];

  if (lReachableRules.length > 0) {
    const lIndexedGraph = new IndexedModuleGraph(pGraph);

    return lReachableRules.reduce(
      (pReturnGraph, pRule) =>
        addReachabilityToGraph(pReturnGraph, lIndexedGraph, pRule),
      structuredClone(pGraph),
    );
  }
  return pGraph;
}
