/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/
/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 1cbebee1-5479-47aa-838e-3c0d5e66e372

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

/-
Sorry-stubbed version for Aristotle independent verification.
Original: FdFormal/FlowerDimension.lean
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['flowerVertCount_eq', 'flowerEdgeCount_eq_pow', 'flowerVertCount_lower', 'flowerVertCount_pos', 'flowerHubDist_eq_pow', 'harmonicSorry379376', 'flowerVertCount_upper']-/
set_option relaxedAutoImplicit false

set_option autoImplicit false

open Real Filter Topology

-- Inline dependencies from FlowerCounts
def flowerEdgeCount (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => (u + v) * flowerEdgeCount u v g

def flowerVertCount (u v : ℕ) : ℕ → ℕ
  | 0 => 2
  | g + 1 => flowerVertCount u v g + (u + v - 2) * flowerEdgeCount u v g

-- Inline dependency from FlowerDiameter
def flowerHubDist (u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | g + 1 => u * flowerHubDist u v g

-- Assumed lemmas (proved in other files, provided as axioms for this challenge)
axiom flowerEdgeCount_eq_pow (u v g : ℕ) :
    flowerEdgeCount u v g = (u + v) ^ g

axiom flowerVertCount_eq (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g =
    (u + v - 2) * (u + v) ^ g + (u + v)

axiom flowerVertCount_pos (u v g : ℕ) :
    0 < flowerVertCount u v g

axiom flowerVertCount_lower (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 2) * (u + v) ^ g ≤
    (u + v - 1) * flowerVertCount u v g

axiom flowerVertCount_upper (u v g : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    (u + v - 1) * flowerVertCount u v g ≤
    2 * (u + v - 1) * (u + v) ^ g

axiom flowerHubDist_eq_pow (u v g : ℕ) :
    flowerHubDist u v g = u ^ g

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  flowerVertCount
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  u-/
-- ℝ bounds
theorem flowerVertCount_lower_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(u + v) - 2 : ℝ) * (↑(u + v) : ℝ) ^ g ≤
    (↑(u + v) - 1 : ℝ) * (↑(flowerVertCount u v g) : ℝ) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  flowerVertCount
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  u-/
theorem flowerVertCount_upper_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(u + v) - 1 : ℝ) * (↑(flowerVertCount u v g) : ℝ) ≤
    2 * (↑(u + v) - 1 : ℝ) * (↑(u + v) : ℝ) ^ g := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  flowerVertCount
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  u-/
theorem flowerVertCount_ge_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(u + v) - 2) / (↑(u + v) - 1) * (↑(u + v) : ℝ) ^ g ≤
    ↑(flowerVertCount u v g) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  flowerVertCount
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  u-/
theorem flowerVertCount_le_real (u v g : ℕ) (hu : 1 < u)
    (huv : u ≤ v) :
    (↑(flowerVertCount u v g) : ℝ) ≤ 2 * (↑(u + v) : ℝ) ^ g := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  Tendsto
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun g : ℕ ↦ log ↑(flowerVertCount u v g) / log ↑(flowerHubDist u v g))-/
-- Headline theorem
theorem flowerDimension (u v : ℕ) (hu : 1 < u) (huv : u ≤ v) :
    Tendsto
      (fun g : ℕ ↦
        log ↑(flowerVertCount u v g) /
        log ↑(flowerHubDist u v g))
      atTop
      (nhds (log ↑(u + v) / log ↑u)) := by
  sorry
