// Parse-tree evidence for the workspace page: turns the engine's proofs
// (ui_proofs.serialize_finding, via GET /api/proof) into ordinary parse trees,
// and lays two trees out over one shared row of witness tokens.
//
// A tree node is {nt, rule, children} for a nonterminal expanded by rule
// number `rule` (0-based, the workspace's order), {t} for a terminal, or
// {eps: true} for the empty string. Works as a browser script
// (window.ParseTrees) and as a Node module.
(function (root, factory) {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.ParseTrees = api;
}(typeof globalThis !== "undefined" ? globalThis : this, function () {
  "use strict";

  // "P001" -> 0. The server numbers productions in the order they were posted.
  function ruleIndex(productionId) {
    const match = /^P(\d+)$/.exec(String(productionId));
    return match ? Number(match[1]) - 1 : null;
  }

  // The engine's right-hand sides are left-nested binary concatenations;
  // flatten them so every node has one child per right-hand-side symbol.
  function body(node, rename) {
    switch (node.kind) {
      case "concatenation":
      case "union":
      case "parentheses":
        return node.children.flatMap((child) => body(child, rename));
      case "terminal":
        return [{ t: rename(node.symbol) }];
      case "epsilon":
        return [{ eps: true }];
      case "nonterminal":
      case "production":
        return [expand(node, rename)];
      default:
        throw new Error(`Unknown derivation node "${node.kind}"`);
    }
  }

  function expand(node, rename) {
    const children = node.children.flatMap((child) => body(child, rename));
    return { nt: node.symbol, rule: ruleIndex(node.production_id), children: children.length ? children : [{ eps: true }] };
  }

  const label = (node) => (node.t !== undefined ? node.t : node.eps ? "ε" : node.nt);

  /* A proof as the evidence panel shows it:
       {id, kind, owner, level, witness, rules, trees: [{root, rule, cut}], partial}
     rules are the 0-based rule numbers at the ambiguity site (two for a union,
     one for a concatenation); each tree's rule is the rule at its root, and a
     concatenation tree's cut is the number of witness tokens before its split.
     postedRules ([{lhs, rhs: [names]}], in posted order) tell whether a
     concatenation covers its whole rule; rename maps posted terminal names
     back to the names shown in the workspace. */
  function normalizeProof(proof, postedRules, rename = (name) => name) {
    const rules = (proof.production_ids || []).map(ruleIndex);
    const witness = proof.witness.map(rename);
    const base = { id: proof.id, kind: proof.kind, owner: proof.owner, level: proof.level, witness, rules, partial: false };
    if (proof.kind === "union") {
      return {
        ...base,
        trees: proof.derivations.map((derivation) => {
          const tree = expand(derivation, rename);
          return { root: tree, rule: tree.rule, cut: null };
        }),
      };
    }
    // A concatenation's trees are rooted at the ambiguous product inside its
    // rule. When the product is the whole right-hand side, root it at the rule.
    const rule = rules[0];
    const rhs = postedRules[rule] ? postedRules[rule].rhs : null;
    let partial = false;
    const trees = proof.factorizations.map((factorization) => {
      const children = body(factorization.derivation, rename);
      const whole = rhs && children.length === rhs.length;
      partial = partial || !whole;
      const nt = whole ? proof.owner : (rhs ? rhs.slice(0, children.length).join(" ") : children.map(label).join(" "));
      return { root: { nt, rule, children, partial: !whole }, rule, cut: factorization.left.length };
    });
    return { ...base, trees, partial };
  }

  function leaves(tree, out = []) {
    if (!tree.children) out.push(tree);
    else tree.children.forEach((child) => leaves(child, out));
    return out;
  }

  function depthOf(tree) {
    return tree.children ? 1 + Math.max(...tree.children.map(depthOf)) : 0;
  }

  /* Lay out trees that derive the same tokens. Every leaf sits on the bottom
     row; a token has the same x in every tree, and ε leaves get their own
     narrow slots between tokens. Each node is centred over the leaves it
     covers, and those leaves are widened until its label fits, so labels on a
     row never overlap.

     measure(node) gives a node's label width in pixels. Returns {width,
     height, rowHeight, tokens: [{x, width}], trees: [{nodes, edges, cutX}]},
     where a node is {node, x, y, width, leaf, depth}. */
  function layoutTrees(trees, measure, options = {}) {
    const row = options.rowHeight || 54;
    const space = options.space || 10;        // between neighbouring leaves
    const padding = options.padding || 10;    // around the whole drawing
    const epsWidth = options.epsWidth || 24;

    // Leaves of each tree in order: tokens are numbered; an ε leaf belongs to
    // the gap before token `gap` and is the `slot`-th ε leaf of that gap.
    const tokenCount = Math.max(0, ...trees.map((tree) => leaves(tree.root).filter((leaf) => !leaf.eps).length));
    const gapWidth = new Array(tokenCount + 1).fill(0);
    const tokenWidth = new Array(tokenCount).fill(0);
    const placed = trees.map((tree) => {
      const where = new Map();
      const perGap = new Array(tokenCount + 1).fill(0);
      let token = 0;
      for (const leaf of leaves(tree.root)) {
        if (leaf.eps) where.set(leaf, { gap: token, slot: perGap[token]++ });
        else {
          tokenWidth[token] = Math.max(tokenWidth[token], measure(leaf) + space);
          where.set(leaf, { token: token++ });
        }
      }
      perGap.forEach((count, gap) => { gapWidth[gap] = Math.max(gapWidth[gap], count * epsWidth); });
      return { where, perGap };
    });

    // x of each unit's left edge: gap 0, token 0, gap 1, token 1, ... gap n.
    const starts = () => {
      const tokenX = [];
      const gapX = [];
      let x = padding;
      for (let i = 0; i <= tokenCount; i++) {
        gapX.push(x);
        x += gapWidth[i];
        if (i < tokenCount) {
          tokenX.push(x);
          x += tokenWidth[i];
        }
      }
      return { tokenX, gapX, right: x };
    };

    // A leaf's horizontal extent in one tree.
    const extent = (tree, leaf, at) => {
      const spot = placed[tree].where.get(leaf);
      if (spot.token !== undefined) return [at.tokenX[spot.token], at.tokenX[spot.token] + tokenWidth[spot.token]];
      const count = placed[tree].perGap[spot.gap];
      const each = gapWidth[spot.gap] / count;
      const left = at.gapX[spot.gap] + each * spot.slot;
      return [left, left + each];
    };

    // Widen leaves until every inner label fits over the leaves it covers,
    // smallest spans first so inner nodes claim their room before outer ones.
    const inner = [];
    trees.forEach((tree, index) => {
      (function visit(node) {
        if (!node.children) return;
        inner.push({ tree: index, node, leaves: leaves(node) });
        node.children.forEach(visit);
      }(tree.root));
    });
    inner.sort((a, b) => a.leaves.length - b.leaves.length);
    for (const item of inner) {
      const at = starts();
      const first = extent(item.tree, item.leaves[0], at);
      const last = extent(item.tree, item.leaves[item.leaves.length - 1], at);
      const deficit = measure(item.node) + space - (last[1] - first[0]);
      if (deficit <= 0) continue;
      const spots = item.leaves.map((leaf) => placed[item.tree].where.get(leaf));
      const tokens = [...new Set(spots.filter((spot) => spot.token !== undefined).map((spot) => spot.token))];
      if (tokens.length) tokens.forEach((token) => { tokenWidth[token] += deficit / tokens.length; });
      else {
        // Only ε leaves: widen their gap so their share of it grows by the deficit.
        const gap = spots[0].gap;
        gapWidth[gap] += deficit * placed[item.tree].perGap[gap] / spots.length;
      }
    }

    const at = starts();
    const depth = Math.max(...trees.map((tree) => depthOf(tree.root)));
    const bottom = padding + depth * row;
    const result = trees.map((tree, index) => {
      const nodes = [];
      const edges = [];
      (function visit(node, level, parent) {
        const covered = leaves(node);
        const left = extent(index, covered[0], at)[0];
        const right = extent(index, covered[covered.length - 1], at)[1];
        const box = { node, x: (left + right) / 2, y: node.children ? padding + level * row : bottom,
                      width: measure(node), leaf: !node.children, depth: level };
        nodes.push(box);
        if (parent) edges.push({ from: parent, to: box });
        if (node.children) node.children.forEach((child) => visit(child, level + 1, box));
      }(tree.root, 0, null));
      // A concatenation splits before the product's last symbol, its right
      // factor, so the marker goes between the last two children's leaves
      // (which also puts any ε leaves on their own factor's side).
      let cutX = null;
      const kids = tree.root.children;
      if (tree.cut !== null && tree.cut !== undefined && kids && kids.length >= 2) {
        const left = leaves(kids[kids.length - 2]);
        const right = leaves(kids[kids.length - 1]);
        cutX = (extent(index, left[left.length - 1], at)[1] + extent(index, right[0], at)[0]) / 2;
      }
      return { nodes, edges, cutX };
    });
    return {
      width: at.right + padding,
      height: bottom + padding + row / 2,
      rowHeight: row,
      bottom,
      tokens: at.tokenX.map((x, i) => ({ x, width: tokenWidth[i] })),
      trees: result,
    };
  }

  return { ruleIndex, normalizeProof, layoutTrees, leaves, label };
}));
