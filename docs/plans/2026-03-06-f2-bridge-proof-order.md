# F2 Bridge Proof Order — Option C (Hub-first)

**Date:** 2026-03-06
**Status:** Approved by auditor

## Proof order

```
walk_hubs → dist_ge → dist_hubs → connected
```

## Dependency graph

```
gadget_adj_chain (proved, Batch 3C)
        │
        ▼
flowerGraph'_walk_hubs ──────────────────────┐
        │                                    │
        │ (hub reachability)                 │
        ▼                                    │
flowerGraph'_dist_ge                         │
        │  uses: Reachable.exists_walk_      │
        │  length_eq_dist, project_adj_or_eq │
        ▼                                    │
flowerGraph'_dist_hubs ◄─────────────────────┘
        │  (upper + lower bound)
        ▼
flowerGraph_dist_hubs (F2 bridge on Fin)

flowerGraph'_connected (structural corollary, proved last)
        ▲
        │ every vertex reaches a hub + hubs reach each other
        │
flowerGraph'_walk_hubs
```

## Why Option C

1. `Reachable.exists_walk_length_eq_dist` lets us extract a shortest
   hub-to-hub walk using only reachability (from `walk_hubs`), not
   global `Connected`. This avoids proving connectivity too early.

2. Stays in `dist : N` throughout — avoids `edist : N∞` pain
   (documented in `MEMORY.md`).

3. `connected` becomes a downstream structural corollary, not a
   prerequisite. Its proof is easier once hub reachability is known.

## `gadget_adj_chain` as step-replacement engine

`gadget_adj_chain` produces a chain of `u + 1` vertices through the
short path of a replacement gadget: position 0 is the embedded parent
source, position u is the embedded parent target, and consecutive
positions are adjacent. In `walk_hubs`, the inductive step replaces
each edge of the gen-g walk with this chain (u adjacencies), giving
total length u * u^g = u^(g+1). The projection argument in `dist_ge`
is an inductive generation-compression: project a shortest hub walk
along `FlowerVert.project`, obtaining a walk in the previous
generation whose length does not increase, then apply induction on g.

## Key API

- `SimpleGraph.dist_le`: walk of length n implies dist <= n
- `Reachable.exists_walk_length_eq_dist`: shortest walk for reachable pair
- `Walk.append`, `Walk.length_append`: walk composition
- `project_adj_or_eq`: adjacency preserved or collapsed under projection
