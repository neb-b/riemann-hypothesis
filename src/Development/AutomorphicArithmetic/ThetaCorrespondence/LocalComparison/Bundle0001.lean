module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
section
theorem UpperTheory.Lit.Cmp.locTied6 : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied l P AI) → Nonempty (Formalism.BasicNotions.LocTied6 l P AI) :=
  Formalism.BasicNotions.CmpTie.locTied6_F
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTiedOf6
section
theorem UpperTheory.Lit.Cmp.locTied_of6 : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  Formalism.BasicNotions.CmpTie.local_comparison_from_alternative
end

