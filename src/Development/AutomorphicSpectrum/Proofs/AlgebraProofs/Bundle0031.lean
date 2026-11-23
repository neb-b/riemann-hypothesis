module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0027
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.LineFibre
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0009
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLattice
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem ideal_le (R : Subalgebra o Ω) (p : ℕ) (hp : p.Prime) (hp0 : (p : Ω) ≠ 0)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (A B : AddSubgroup Ω) (hB : LocFree R 1 B) (hA : ∀ a ∈ A, a ∈ R) (hm : ∃ m : ℕ, (p : Ω) ^ m ∈ B)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → spanOver RC (algebraMap Ω C '' A) = spanOver RC (algebraMap Ω C '' B)) :
    A ≤ B := by
  intro v hv
  obtain ⟨m, hm⟩ := hm
  refine GlobalTheory.CompanionTheory.Ar.Num.HaTest.mem_of_test_ideal R p hp hp0 hN hF hI B hB v ⟨m, ?_⟩ ?_
  · have := hB.1 v (hA v hv) _ hm
    rwa [smul_eq_mul, mul_comm] at this
  · intro C _ _ _ _ RC hRC
    rw [← h C RC hRC]
    exact mem_span RC ⟨v, hv, rfl⟩

theorem lattice_le (R : Subalgebra o Ω) (p : ℕ) (hp : p.Prime) (hp0 : (p : Ω) ≠ 0)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    {k N : ℕ} (L A B : AddSubgroup (Fin k → Ω)) (hB : LocFree R N B) (hA : A ≤ L)
    (hm : mulLat (p : Ω) L ≤ B)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → spanOver RC (bcMap Ω C (Fin k) '' A) = spanOver RC (bcMap Ω C (Fin k) '' B)) :
    A ≤ B := by
  intro v hv
  refine GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI N B hB v ⟨1, ?_⟩ ?_
  · rw [pow_one]
    exact hm ⟨v, hA hv, rfl⟩
  · intro C _ _ _ _ RC hRC
    rw [← h C RC hRC]
    exact mem_span RC ⟨v, hv, rfl⟩

omit [Algebra o Ω] in
theorem map_snd_span {C : Type} [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C) {k : ℕ}
    (G : AddSubgroup (Ω × (Fin k → Ω))) :
    (spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin k)) '' G)).map (AddMonoidHom.snd _ _) =
      spanOver RC (bcMap Ω C (Fin k) '' (G.map (AddMonoidHom.snd _ _))) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨g.2, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
  {D : LieLatticeData Ω F n Sg r s} {R : Subalgebra o Ω} {p : ℕ} {w : Ω} {χ : Sg → F → Ω}

theorem xId_le (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∀ c ∈ D.xId (χ τ) i, c ∈ R := by
  intro c hc'
  have h : (c • fun x : Fin n → F => χ τ (x i)) ∈
    D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup := hc'
  obtain ⟨g, hg, v, hv, e⟩ := AddSubgroup.mem_sup.1 h
  have hx : (Pi.single i (1 : F) : Fin n → F) ∈
      {x : Fin n → F | ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0} := by
    intro j hj
    have : j ≠ i := by
      rintro rfl
      omega
    exact Pi.single_eq_of_ne this _
  have hv0 : v (Pi.single i 1) = 0 := hv _ hx
  have hgR : g (Pi.single i 1) ∈ R := hb.M_le hg _ (Set.mem_univ _)
  have e1 := congrFun e (Pi.single i 1)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, hv0, add_zero, smul_eq_mul,
    (hc.2.2.2.2 τ).2.1, mul_one] at e1
  rwa [← e1]

theorem pow_smul_mem (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, ((p : Ω) ^ m • fun x : Fin n → F => χ τ (x i)) ∈ D.M := by
  obtain ⟨m, hm⟩ := hb.le_M
  exact ⟨m, hm ⟨fun x => χ τ (x i), fun x _ => (hc.2.2.2.2 τ).2.2 _, rfl⟩⟩

theorem pow_mem_xId (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ D.xId (χ τ) i := by
  obtain ⟨m, hm⟩ := pow_smul_mem hc hb τ i
  exact ⟨m, AddSubgroup.mem_sup_left hm⟩

theorem pow_mem_dId (hc : CharData R p w χ) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ D.dId R p (χ τ) i := by
  refine ⟨1, (p : Ω) • Pi.single i 1, ⟨?_, ?_⟩, ?_⟩
  · show linMap n (χ τ) ((p : Ω) • Pi.single i 1) ∈ D.l1 R p
    rw [map_smul]
    refine AddSubgroup.mem_sup_right ⟨linMap n (χ τ) (Pi.single i 1), fun x _ => ?_, rfl⟩
    show linMap n (χ τ) (Pi.single i 1) x ∈ R
    simp only [linMap, Fintype.linearCombination_apply_single, one_smul]
    exact (hc.2.2.2.2 τ).2.2 _
  · intro j hj
    have : j ≠ i := by
      rintro rfl
      exact Nat.lt_irrefl _ hj
    show ((p : Ω) • Pi.single i (1 : Ω) : Fin n → Ω) j = 0
    simp [Pi.single_eq_of_ne this]
  · simp

omit [One F] in
theorem kk_le (hb : D.Base R p w) (τ : Sg) (i : ℕ) : D.kk τ i ≤ dotDual R (D.lie τ) := by
  rintro _ ⟨⟨g, m⟩, ⟨h, -⟩, rfl⟩
  exact ((hb.th τ).2.1 m).1 ⟨g, h⟩

omit [One F] in
theorem le_kk (hb : D.Base R p w) (τ : Sg) (i : ℕ) :
    mulLat (p : Ω) (dotDual R (D.lie τ)) ≤ D.kk τ i := by
  intro m hm
  exact ⟨(0, m), ⟨((hb.th τ).2.2 m).2 hm, zero_mem _, trivial⟩, rfl⟩

omit [One F] in
theorem step_le (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    (D.stepGraph τ ψ i).map (AddMonoidHom.snd _ _) ≤ dotDual R (D.lie τ) := by
  rintro _ ⟨⟨c, m⟩, h, rfl⟩
  have h' : ((c • fun x : Fin n → F => ψ (x i)), m) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := h
  obtain ⟨⟨g, m1⟩, hg, ⟨v, m2⟩, ⟨-, hv⟩, e⟩ := AddSubgroup.mem_sup.1 h'
  have h2 : m2 = 0 := hv
  have h1 : m1 + m2 = m := congrArg Prod.snd e
  rw [h2, add_zero] at h1
  subst h1
  exact ((hb.th τ).2.1 m1).1 ⟨g, hg⟩

omit [One F] in
theorem le_step (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    mulLat (p : Ω) (dotDual R (D.lie τ)) ≤ (D.stepGraph τ ψ i).map (AddMonoidHom.snd _ _) := by
  intro m hm
  refine ⟨(0, m), ?_, rfl⟩
  show (((0 : Ω) • fun x : Fin n → F => ψ (x i)), m) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥
  rw [zero_smul]
  exact AddSubgroup.mem_sup_left (((hb.th τ).2.2 m).2 hm)

omit [One F] in
theorem ker_le (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    (D.stepGraph τ ψ i).comap (AddMonoidHom.inl _ _) ≤ D.xId ψ i := by
  intro c h
  have h' : ((c • fun x : Fin n → F => ψ (x i)), (0 : Fin (r τ) → Ω)) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := h
  obtain ⟨⟨g, m1⟩, hg, ⟨v, m2⟩, ⟨hv, -⟩, e⟩ := AddSubgroup.mem_sup.1 h'
  have h1 : g + v = c • fun x : Fin n → F => ψ (x i) := congrArg Prod.fst e
  show (c • fun x : Fin n → F => ψ (x i)) ∈ D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup
  rw [← h1]
  exact AddSubgroup.add_mem_sup (((hb.th τ).1 g).1 ⟨m1, hg⟩).1 hv

theorem pow_mem_ker (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
  obtain ⟨m, hm⟩ := pow_smul_mem hc hb τ i
  obtain ⟨u, hu⟩ := ((hb.th τ).1 _).2 ⟨hm, by simp [(hc.2.2.2.2 τ).1]⟩
  have h1 := (hb.stable τ (p : Ω) (natCast_mem R p)).2.2 _ hu
  have h2 := ((hb.th τ).2.2 ((p : Ω) • u)).2 ⟨u, ((hb.th τ).2.1 u).1 ⟨_, hu⟩, rfl⟩
  have h3 := sub_mem h1 h2
  refine ⟨m + 1, ?_⟩
  show (((p : Ω) ^ (m + 1) • fun x : Fin n → F => χ τ (x i)), (0 : Fin (r τ) → Ω)) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥
  refine AddSubgroup.mem_sup_left ?_
  rw [Prod.smul_mk, Prod.mk_sub_mk, sub_zero, sub_self, smul_smul, ← pow_succ'] at h3
  exact h3

theorem powSpan_le (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) (hX : ∀ c ∈ X, c ∈ R) :
    ∀ c ∈ powSpan R p X, c ∈ R := by
  have : powSpan R p X ≤ R.toSubring.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact R.mul_mem ha (R.pow_mem (hX x hx) p)
  exact fun c hc => this hc

end GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices


open GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices in
theorem GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i) ∧ (∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i) ∧ ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan R p (D.xId (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2
  obtain ⟨hf1, hbc1⟩ := GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hc hb hG
  have hk := GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change D R p w χ hc hb hG
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main D R p w χ hc hb hG hG2
    (GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice D R p w χ hc hb hp hN hF hI φ hT hG)
  have hp0 := hc.1
  refine ⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_⟩
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) =
          spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
      intro C _ _ _ _ RC hRC
      rw [← (((hbc2 C RC hRC.2.2.2).2 τ).2 i).1, ← ((hbc1 C RC hRC.2.2.2).2 τ).2.2 i]
      exact (hT C RC hRC).dx τ i
    refine le_antisymm
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf1 τ).2.2.2 i) ?_ (pow_mem_xId hc hb τ i) h)
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf2 τ).2 i).1 (xId_le hc hb τ i) (pow_mem_dId hc τ i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
    rintro _ ⟨l, ⟨hl, -⟩, rfl⟩
    exact (hf1 τ).2.2.1 hl i (Set.mem_univ _)
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (bcMap Ω C (Fin (r τ)) '' (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) =
          spanOver RC (bcMap Ω C (Fin (r τ)) '' D.kk τ i) := by
      intro C _ _ _ _ RC hRC
      rw [← map_snd_span, ← (hk C RC hRC.2.2.2 τ).2 i, ← (hk C RC hRC.2.2.2 τ).1 i]
      exact (hT C RC hRC).onto τ i
    exact le_antisymm
      (lattice_le R p hp hp0 hN hF hI _ _ _ (hG2.kk τ i) (step_le hb τ _ i) (le_kk hb τ i) h)
      (lattice_le R p hp hp0 hN hF hI _ _ _ (hG2.step τ i) (kk_le hb τ i) (le_step hb τ _ i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (algebraMap Ω C ''
            (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _)) =
          spanOver RC (algebraMap Ω C '' powSpan R p (D.xId (χ τ) i)) := by
      intro C _ _ _ _ RC hRC
      rw [← (((hbc2 C RC hRC.2.2.2).2 (φ τ)).2 i).2,
        ← (GlobalTheory.CompanionTheory.Ar.Num.powSpan_locFree_baseChange R RC hRC.2.2.2 p _ ((hf1 τ).2.2.2 i)).2,
        ← ((hbc1 C RC hRC.2.2.2).2 τ).2.2 i]
      exact (hT C RC hRC).inj τ i
    obtain ⟨m, hm⟩ := pow_mem_xId hc hb τ i
    refine le_antisymm
      (ideal_le R p hp hp0 hN hF hI _ _
        (GlobalTheory.CompanionTheory.Ar.Num.powSpan_locFree_baseChange (C := Ω) R R (fun _ ha => ha) p _ ((hf1 τ).2.2.2 i)).1
        (fun a ha => xId_le hc hb (φ τ) i a (ker_le hb _ _ i ha)) ⟨m * p, ?_⟩ h)
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf2 (φ τ)).2 i).2
        (powSpan_le R p _ (xId_le hc hb τ i)) (pow_mem_ker hc hb (φ τ) i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
    rw [pow_mul]
    exact mem_span R ⟨_, hm, rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderIdealsEqTopStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top | exact GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBaseStatement
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_lattice_base : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | exact GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsoPowOneLawFormula
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem iso_pow_one_law : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.iso_first_power

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineFibreHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem lineFibre_holds : ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.LineFibre.full

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineIsomorphismGroupoidLaws
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem lineIso_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) :=
  @PositivityTheory.UnitarySelfGeneration.i_algebra

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalComparisonOfOrbitsHolds
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem orbit_map_pow {A B : Type} (e : A → B) (a : Equiv.Perm A) (b : Equiv.Perm B)
    (he : ∀ t, e (a t) = b (e t)) (n : ℕ) (t : A) : e ((a ^ n) t) = (b ^ n) (e t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he, ih]

theorem local_comparison_of_orbits : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  intro O _ _ _ K _ _ ι _ Sg _ _ P d p hp φ r s lie om hrel k hk Q hQ τ
  obtain ⟨Sg', hfin, e, φ', ⟨t0, ht0⟩, hcomm, hR⟩ := hrel τ
  subst ht0
  haveI : Fintype Sg' := Fintype.ofFinite Sg'
  obtain ⟨h, h1, h2⟩ := hR k hk Q hQ
  obtain ⟨La, hLa⟩ : ∃ La : Sg → ℝ, La = fun σ => ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := ⟨_, rfl⟩
  have hLa' : ∀ σ, La σ = ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := fun σ => by rw [hLa]
  have h1' : ∀ t, (((lie (e t)).ck P k Q : ℤ) : ℝ) + (((om (e t)).ck P k Q : ℤ) : ℝ)
      = h t - ((laNum P (p : O) (lie (e t)).x k Q : ℤ) : ℝ) / ((p : ℝ) - 1) := fun t => h1 t
  have h2' : ∀ t, (p : ℝ) ^ k * h t = h (φ' t) + La (e (φ' t)) := by
    intro t
    rw [hLa']
    exact h2 t
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have hpk0 : (p : ℝ) ^ k ≠ 0 := (zero_lt_one.trans hpk).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((p : ℝ) ^ k)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact inv_nonneg.mpr (zero_lt_one.trans hpk).le
  have hc1 : c < 1 := by
    rw [hc]
    exact inv_lt_one_of_one_lt₀ hpk
  have hrec : ∀ t, h t = c * (h (φ' t) + La (e (φ' t))) := by
    intro t
    rw [hc, ← h2' t, ← mul_assoc, inv_mul_cancel₀ hpk0, one_mul]
  have hpart : ∀ N t, h t = (∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t)))
      + c ^ N * h ((φ' ^ N) t) := by
    intro N
    induction N with
    | zero => intro t; simp
    | succ N ih =>
      intro t
      have hstep : φ' ((φ' ^ N) t) = (φ' ^ (N + 1)) t := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [ih t, Finset.sum_range_succ, hrec ((φ' ^ N) t), hstep]
      ring
  have hbd : ∀ f : Sg' → ℝ, ∀ t, |f t| ≤ ∑ u, |f u| := fun f t =>
    Finset.single_le_sum (f := fun u => |f u|) (fun u _ => abs_nonneg (f u)) (Finset.mem_univ t)
  have hsum : Summable (fun n : ℕ => c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0))) := by
    have hg : Summable (fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) := by
      refine ((summable_geometric_of_lt_one hc0 hc1).mul_left ((∑ u, |La (e u)|) * c)).congr
        (fun n => ?_)
      ring
    refine Summable.of_norm_bounded (g := fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) hg
      (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |La (e u)|)]
    exact mul_le_mul_of_nonneg_left (hbd (fun u => La (e u)) _) (pow_nonneg hc0 _)
  have hlim1 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hz : Filter.Tendsto (fun N : ℕ => c ^ N * h ((φ' ^ N) t0)) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun N : ℕ => (∑ u, |h u|) * c ^ N) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (∑ u, |h u|)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm (fun N => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |h u|)]
    exact mul_le_mul_of_nonneg_left (hbd h _) (pow_nonneg hc0 _)
  have hlim2 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (h t0)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => h t0) Filter.atTop (nhds (h t0)) := tendsto_const_nhds
    have := hconst.sub hz
    rw [sub_zero] at this
    refine this.congr (fun N => ?_)
    rw [hpart N t0]
    ring
  have hh : h t0 = ∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)) := tendsto_nhds_unique hlim2 hlim1
  have hh2 : h t0 = ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) (e t0)) := by
    rw [hh, hc]
    refine tsum_congr (fun n => ?_)
    rw [orbit_map_pow e φ' φ hcomm]
  have key := (co_series_three_step).1 Sg φ p k hp hk La (e t0)
  have final : (((lie (e t0)).ck P k Q : ℤ) : ℝ) + (((om (e t0)).ck P k Q : ℤ) : ℝ)
      = ∑ σ, GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (e t0) σ * La σ := by
    rw [key, h1' t0, hh2, hLa' (e t0)]
  subst hLa
  exact final

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOnePowTwoCommutation
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_interchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) :=
  PositivityTheory.HtPt.Cc.pow_inter

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelation
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_sy_exchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.pow_sy

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactEigenSubDegree
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eigen_ses_subDeg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ (ρ : O → V →ₗ[K] V) (ρ' : O →+* Module.End K V') (ρ'' : O → V'' →ₗ[K] V''), IsBun C L' → (∀ a, IsHom C L' L' (ρ' a)) → ShortExact C L L' L'' f g → (∀ a x, f (ρ a x) = ρ' a (f x)) → (∀ a y, g (ρ' a y) = ρ'' a (g y)) → ∀ s, subDeg C L' (eig (fun a => ρ' a) (fun a => algebraMap k K (χ s a))) = subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) + subDeg C L'' (eig (fun a => ρ'' a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_ses

end GlobalTheory.CompanionTheory.Ar.Crv
end

