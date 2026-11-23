module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLConj
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.UnitProd

private theorem equivalence_twisted_conj {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  constructor
  · intro x
    exact ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem rep_mk {G : Type} [Group G] (θ : G →* G) (x : G) :
    ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g := by
  unfold TwCl.rep
  have h := Quot.eqvGen_exact (Quot.out_eq (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x))
  rw [Equivalence.eqvGen_iff (equivalence_twisted_conj θ)] at h
  exact (equivalence_twisted_conj θ).symm h

theorem mk_rep {G : Type} [Group G] {θ : G →* G} (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := by
  unfold TwCl.rep
  exact Quot.out_eq c

noncomputable def clsEquiv {G G' : Type} [Group G] [Group G'] (θ : G →* G) (θ' : G' →* G') :
    TwCl θ × TwCl θ' ≃ TwCl (θ.prodMap θ') where
  toFun p := Quot.mk _ (p.1.rep, p.2.rep)
  invFun c := (Quot.mk _ c.rep.1, Quot.mk _ c.rep.2)
  left_inv p := by
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    refine Prod.ext ?_ ?_
    · refine Eq.trans (Quot.sound ⟨g.1, ?_⟩).symm (mk_rep p.1)
      exact congrArg Prod.fst hg
    · refine Eq.trans (Quot.sound ⟨g.2, ?_⟩).symm (mk_rep p.2)
      exact congrArg Prod.snd hg
  right_inv c := by
    obtain ⟨g, hg⟩ := rep_mk θ c.rep.1
    obtain ⟨g', hg'⟩ := rep_mk θ' c.rep.2
    refine Eq.trans (Quot.sound ⟨(g, g'), ?_⟩).symm (mk_rep c)
    refine Prod.ext ?_ ?_
    · simp [hg]
    · simp [hg']

theorem ind_conj {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x k : G) (hk : k ∈ K) :
    (x * k)⁻¹ * δ * θ (x * k) ∈ K ↔ x⁻¹ * δ * θ x ∈ K := by

  have e : (x * k)⁻¹ * δ * θ (x * k) = k⁻¹ * (x⁻¹ * δ * θ x) * θ k := by
    rw [map_mul]; group
  rw [e, K.mul_mem_cancel_right (hK k hk), K.mul_mem_cancel_left (K.inv_mem hk)]

theorem index_ne {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by

  have htop : rStab (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))) = ⊤ := by
    ext k
    simp only [Subgroup.mem_top, iff_true]
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro y
    simp only [Subgroup.coe_mul, ← mul_assoc]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [SetLike.mem_coe, ind_conj θ K hK δ (x * y) k k.2, Pi.one_apply]
  rw [htop, Subgroup.index_top]
  exact one_ne_zero

theorem clSum_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (S : Set G) (S' : Set G') (hK : ∀ k ∈ K, θ k ∈ K) (hK' : ∀ k ∈ K', θ' k ∈ K')
    (hS : ∀ g y, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) (hS' : ∀ g y, g⁻¹ * y * θ' g ∈ S' ↔ y ∈ S')
    (hf : {c : TwCl θ | c.rep ∈ S}.Finite) (hf' : {c : TwCl θ' | c.rep ∈ S'}.Finite)
    (hd : ∀ y ∈ S, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      (Quotient.out q)⁻¹ * y * θ (Quotient.out q) ∈ K}.Finite)
    (hd' : ∀ y ∈ S', {q : DoubleCoset.Quotient (twCent θ' y : Set G') (K' : Set G') |
      (Quotient.out q)⁻¹ * y * θ' (Quotient.out q) ∈ K'}.Finite) :
    clSum (θ.prodMap θ') (K.prod K') {y | y.1 ∈ S ∧ y.2 ∈ S'} 1 (((K.prod K' : Subgroup _) : Set _).indicator 1) =
      clSum θ K S 1 ((K : Set G).indicator 1) * clSum θ' K' S' 1 ((K' : Set G').indicator 1) := by
  unfold clSum
  simp only [Pi.one_apply, one_mul]

  have hKK : ∀ k ∈ K.prod K', (θ.prodMap θ') k ∈ K.prod K' := fun k hk =>
    Subgroup.mem_prod.mpr ⟨hK _ (Subgroup.mem_prod.mp hk).1, hK' _ (Subgroup.mem_prod.mp hk).2⟩
  have hind : (((K.prod K' : Subgroup _) : Set (G × G')).indicator (1 : G × G' → ℂ)) =
      fun y => (K : Set G).indicator 1 y.1 * (K' : Set G').indicator 1 y.2 := by
    funext y
    by_cases h1 : y.1 ∈ K <;> by_cases h2 : y.2 ∈ K' <;>
      simp [Subgroup.mem_prod, h1, h2]
  have hfin : ∀ {H : Type} [Group H] (φ : H →* H) (L : Subgroup H) (hL : ∀ k ∈ L, φ k ∈ L) (T : Set H)
      (hT : ∀ y ∈ T, {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        (Quotient.out q)⁻¹ * y * φ (Quotient.out q) ∈ L}.Finite) (y : H), y ∈ T →
      {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        ∃ k ∈ L, (L : Set H).indicator (1 : H → ℂ) ((Quotient.out q * k)⁻¹ * y * φ (Quotient.out q * k)) ≠ 0}.Finite := by
    intro H _ φ L hL T hT y hy
    refine (hT y hy).subset ?_
    rintro q ⟨k, hk, hne⟩
    by_contra hq
    apply hne
    rw [Set.indicator_apply, if_neg]
    rw [SetLike.mem_coe, ind_conj φ L hL _ _ k hk]
    exact hq
  have hprod : ∀ p : TwCl θ × TwCl θ',
      (if (clsEquiv θ θ' p).rep ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} then
        twOrb (θ.prodMap θ') (K.prod K') (clsEquiv θ θ' p).rep (((K.prod K' : Subgroup _) : Set _).indicator 1)
        else 0) =
      (if p.1.rep ∈ S then twOrb θ K p.1.rep ((K : Set G).indicator 1) else 0) *
      (if p.2.rep ∈ S' then twOrb θ' K' p.2.rep ((K' : Set G').indicator 1) else 0) := by
    intro p
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    have e : (clsEquiv θ θ' p).rep = g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g := hg
    have hmem : g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} ↔
        p.1.rep ∈ S ∧ p.2.rep ∈ S' := by
      show g.1⁻¹ * p.1.rep * θ g.1 ∈ S ∧ g.2⁻¹ * p.2.rep * θ' g.2 ∈ S' ↔ _
      rw [hS, hS']
    rw [e, GlobalTheory.TwOrbConj.twOrb_twConj (G × G') (θ.prodMap θ') (K.prod K') (p.1.rep, p.2.rep) g _
      (fun x => index_ne (θ.prodMap θ') (K.prod K') hKK _ x)]
    by_cases h1 : p.1.rep ∈ S <;> by_cases h2 : p.2.rep ∈ S'
    · simp only [hmem, h1, h2, and_self, if_true]
      rw [hind]
      exact _root_.GlobalTheory.BCT.OrbProd.twOrb_prod G G' θ θ' K K' _ _ _ _ (fun x => index_ne θ K hK _ x) (fun x => index_ne θ' K' hK' _ x)
        (hfin θ K hK S hd _ h1) (hfin θ' K' hK' S' hd' _ h2)
    · rw [if_neg fun h => h2 (hmem.mp h).2, if_neg h2, mul_zero]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
  have hs1 : (Function.support fun c : TwCl θ =>
      if c.rep ∈ S then twOrb θ K c.rep ((K : Set G).indicator 1) else 0).Finite := by
    refine hf.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S at h
    simp [h]
  have hs2 : (Function.support fun c : TwCl θ' =>
      if c.rep ∈ S' then twOrb θ' K' c.rep ((K' : Set G').indicator 1) else 0).Finite := by
    refine hf'.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S' at h
    simp [h]
  rw [← finsum_comp_equiv (clsEquiv θ θ')]
  refine (finsum_congr hprod).trans ?_
  rw [finsum_curry _ ((hs1.prod hs2).subset fun p hp => ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩),
    finsum_mul]
  refine finsum_congr fun c => ?_
  rw [mul_finsum]

theorem charpoly_nrmL_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : Unr E) (n : ℕ) (w : Pl E)
    (g y : GLw n w) : (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hE, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' _ _

theorem stTw2_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)).indicator 1) := by
  intro E _ _ _ hE a b w hw Q₁ Q₂ h₁ h₂
  unfold stTw2 stTw
  have hL : ∀ m : ℕ, IsLevel (thL m w) (GlobalTheory.LFun.KGL w (n := m)) (GlobalTheory.LFun.KGL w (n := m)) := by
    intro m
    unfold IsLevel
    exact ⟨(GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hE m w k hk⟩
  have hS : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (g y : GLw m w),
      g⁻¹ * y * thL m w g ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} ↔
        y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} := by
    intro m Q g y
    show _ = Q ↔ _ = Q
    rw [charpoly_nrmL_conj hE]
  have hd : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]), Q.Separable →
      ∀ y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q},
        {q : DoubleCoset.Quotient (twCent (thL m w) y : Set (GLw m w)) (GlobalTheory.LFun.KGL w (n := m) : Set (GLw m w)) |
          (Quotient.out q)⁻¹ * y * thL m w (Quotient.out q) ∈ GlobalTheory.LFun.KGL w (n := m)}.Finite := by
    intro m Q hQ y hy
    have hy' : (nrmL m w y).val.charpoly = Q := hy
    exact (GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE m w y (hy' ▸ hQ) _ (hL m)).2 _ (GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.2.1
  exact clSum_prod (thL a w) (thL b w) _ _ _ _ (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE a w)
    (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE b w) (hS a Q₁) (hS b Q₂) (GlobalTheory.BCT.ClsFin.classes_finite E hE a w Q₁ h₁).1
    (GlobalTheory.BCT.ClsFin.classes_finite E hE b w Q₂ h₂).1 (hd a Q₁ h₁) (hd b Q₂ h₂)

end GlobalTheory.BCT.UnitProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMonicOperatorPolynomials
section
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.FactorMod

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem finMod_mono {K₁ K₂ : Submodule ℂ M} (h : K₁ ≤ K₂) {A : Subalgebra ℂ (Module.End ℂ M)} {v : M}
    (hf : FinMod K₁ A v) : FinMod K₂ A v := by
  unfold FinMod at *
  have e : Submodule.span ℂ {y : M ⧸ K₂ | ∃ a ∈ A, y = K₂.mkQ (a v)} =
      (Submodule.span ℂ {y : M ⧸ K₁ | ∃ a ∈ A, y = K₁.mkQ (a v)}).map (Submodule.factor h) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨K₁.mkQ (a v), ⟨a, ha, rfl⟩, Submodule.factor_mk h _⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, Submodule.factor_mk h _⟩
  rw [e]
  infer_instance

theorem comm_of_mem_adjoin {s : Set (Module.End ℂ M)} {f b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s)
    (h : ∀ g ∈ s, Commute f g) : Commute f b := by
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {f} :=
    Algebra.adjoin_le fun g hg => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact (h g hg)
  exact (((Subalgebra.mem_centralizer_iff ℂ).1 (hle hb)) f rfl)

def core (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | ∀ b ∈ S, b x ∈ K}
  add_mem' := fun hx hy b hb => by rw [map_add (f := _)]; exact K.add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [map_zero]; exact K.zero_mem
  smul_mem' := fun c x hx b hb => by rw [map_smul]; exact K.smul_mem c (hx b hb)

theorem core_le (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : core K S ≤ K := fun x hx => by
  simpa using hx 1 S.one_mem

theorem finMod_factor : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) → (∀ u u', Commute (c u) (q u')) →
 (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K) →
 (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
 ∀ v ∈ M', FinMod ⊥ (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hcq hM hK hrel v hv hfin
  set S := Algebra.adjoin ℂ (Set.range q) with hS

  have cb : ∀ u, ∀ b ∈ S, Commute (c u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hcq u u')
  have pb : ∀ u, ∀ b ∈ S, Commute (p u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hpq u u')
  have qb : ∀ u, ∀ b ∈ S, Commute (q u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hqq u u')

  have hSM : ∀ b ∈ S, ∀ x ∈ M', b x ∈ M' := by
    have hle : S ≤ GlobalTheory.LeviHC.MidBlock.stab M' :=
      Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩ x hx; exact (hM u x hx).2.2)
    intro b hb x hx
    exact hle hb x hx
  set K' := core K S
  have hK'p : ∀ u, ∀ x ∈ K', p u x ∈ K' ∧ q u x ∈ K' := by
    intro u x hx
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have e : b (p u x) = p u (b x) := by
        have := (pb u b hb).eq
        exact (congrArg (fun f : Module.End ℂ M => f x) this).symm
      rw [e]; exact hK u _ (hx b hb)
    · have : b * q u ∈ S := S.mul_mem hb (Algebra.subset_adjoin ⟨u, rfl⟩)
      exact hx _ this
  have hrel' : ∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K' := by
    intro u x hx b hb
    have e1 : b (c u x) = c u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (cb u b hb).eq).symm
    have e2 : b (q u x) = q u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (qb u b hb).eq).symm
    have e3 : b (p u (q u x)) = p u (b (q u x)) :=
      (congrArg (fun f : Module.End ℂ M => f (q u x)) (pb u b hb).eq).symm
    rw [map_sub, e1, e3, e2]
    exact hrel u _ (hSM b hb x hx)
  have h1 : FinMod K' (Algebra.adjoin ℂ (Set.range c)) v := finMod_mono bot_le hfin
  have h2 := GlobalTheory.LeviHC.QuotMonic.monicFactorFiniteMod_of GlobalTheory.LeviHC.monicFactorFinite M M' K' c p q hp hq hpp hqq hpq
    hM hK'p hrel' v hv h1
  exact finMod_mono (core_le K S) h2

end GlobalTheory.LeviHC.FactorMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.AutomorphicL2Unitary (LeftInv)

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem ratPts_inf_subgroupOf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) :
    (ratPts σ J ⊓ P).subgroupOf N = (ratPts σ J).subgroupOf N := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hNP x.2⟩⟩

theorem isConstTermOn_iff_ratPts_inf {N P : Subgroup (GAd σ J)} [LocallyCompactSpace N] (hNP : N ≤ P)
    (hc : Cocompact (ratPts σ J) N) {φ c : GAd σ J → ℂ} (hφ : LeftInv (ratPts σ J ⊓ P) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J ⊓ P) N φ := by
  have e := ratPts_inf_subgroupOf (σ := σ) (J := J) hNP
  constructor
  · intro h
    obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
    funext g
    rw [h μ 𝓕 h1 h2 h3 g, GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g]
  · rintro rfl μ 𝓕 h1 h2 h3 g
    exact GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g

theorem cocompact_ratPts_inf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) (hc : Cocompact (ratPts σ J) N) :
    Cocompact (ratPts σ J ⊓ P) N := by
  unfold Cocompact
  rw [ratPts_inf_subgroupOf hNP]
  exact hc

section Witt

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem locallyCompact_unip (S : Finset (Fin r)) : LocallyCompactSpace (unip σ J X S) :=
  (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unip_std (S : Finset (Fin r)) : Cocompact (ratPts σ J) (unip σ J X S) := by
  by_cases hS0 : S = ∅
  · subst hS0
    refine ⟨{1}, isCompact_singleton, fun u => ⟨u⁻¹, ?_, by simp⟩⟩
    have hu : (u : GAd σ J) = 1 := Subgroup.mem_bot.1 (le_of_eq (unip_empty (σ := σ) (J := J) (X := X)) u.2)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inv, hu, inv_one]
    exact one_mem _
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  rw [GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW S m hm hm']
  exact cocompact_unipFlag hJ (sigma_sigma h) (isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ m.2) _

theorem conj_mem_unip_of_subset {S T : Finset (Fin r)} (hTS : T ⊆ S) {p u : GAd σ J} (hp : p ∈ unip σ J X S)
    (hu : u ∈ unip σ J X T) : p * u * p⁻¹ ∈ unip σ J X T := by
  by_cases hT0 : T = ∅
  · subst hT0
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eT := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW T m hm hm'
  rw [eT] at hu ⊢
  exact conj_mem_unipFlag hJ hσ (isIsoCols_of_isWittFrame hW hσ hJ m.2) _
    (GlobalTheory.ConstTrans.unip_le_parFlag F E σ h n J hJ r X Y hW S T m hTS hm hm' hp) hu

theorem constAlong_cocompact_unique_stages :
    (∀ S : Finset (Fin r), Cocompact (ratPts σ J) (unip σ J X S) ∧
      ∃ (μ : Measure (unip σ J X S)) (𝓕 : Set (unip σ J X S)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unip σ J X S)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ S T : Finset (Fin r), T ⊆ S → unip σ J X T ≤ unip σ J X S ∧ levi σ J X Y S ≤ levi σ J X Y T) ∧
    (∀ (S : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), IsConstAlong σ J X S φ c → IsConstAlong σ J X S φ c' → c = c') ∧
    (∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ), (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      ∃ c, IsConstAlong σ J X S φ c) ∧
    (∀ (S T : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), T ⊆ S → Continuous φ →
      (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      IsConstAlong σ J X T φ c → IsConstAlong σ J X S c c' → IsConstAlong σ J X S φ c') := by
  refine ⟨fun S => ?_, fun S T hTS => ⟨unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS, ?_⟩,
    fun S φ c c' h1 h2 => ?_, fun S φ hφ => ?_, fun S T φ c c' hTS hφc hφ hc hc' => ?_⟩
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨cocompact_unip_std h hJ hW S, exists_mass_one (cocompact_unip_std h hJ hW S)⟩
  · intro g hg
    simp only [levi, Subgroup.mem_iInf] at hg ⊢
    exact fun k hk => hg k (hTS hk)
  · haveI := locallyCompact_unip h hJ hW S
    exact IsConstTermOn.unique (cocompact_unip_std h hJ hW S) h1 h2
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨_, isConstTermOn_constTermOn (N := unip σ J X S) fun γ hγ g => hφ γ hγ.1 hγ.2 g⟩
  · haveI := locallyCompact_unip h hJ hW S
    haveI := locallyCompact_unip h hJ hW T
    have hle : unip σ J X T ≤ unip σ J X S := unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS
    have cS := cocompact_unip_std h hJ hW S
    have cT := cocompact_unip_std h hJ hW T
    have hfΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) φ := fun γ hγ g => hφ γ hγ.1 hγ.2 g
    have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T :=
      fun p hp u hu => conj_mem_unip_of_subset h hJ hW hTS hp hu
    have hc0 : c = constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ :=
      (isConstTermOn_iff_ratPts_inf hle cT hfΓ).1 hc
    subst hc0
    have hcΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) :=
      fun γ hγ g => GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hfΓ hγ
        (fun m => ⟨hnorm _ hγ.2 m, fun hm => by simpa [mul_assoc] using hnorm _ (inv_mem hγ.2) _ hm⟩) g
    have st : constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) φ =
        constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S)
          (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) := funext fun x =>
      GlobalTheory.Cusp.Stages.constTermOn_stages (GAd σ J) (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) (unip σ J X T) hle hnorm
        (cocompact_ratPts_inf le_rfl cS) (cocompact_ratPts_inf hle cT) φ hfΓ hφc x
    change IsConstTermOn σ J (unip σ J X S) _ c' at hc'
    change IsConstTermOn σ J (unip σ J X S) φ c'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hcΓ] at hc'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hfΓ, st]
    exact hc'

end Witt

end GlobalTheory.StdPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransportCovolumeOneHaarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) →
    ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
    letI : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
    ∃ (lam : MeasureTheory.Measure ((κ → AF D.host.F) × (κ → AF D.host.F)))
      (𝓖 : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
      lam.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) 𝓖 lam ∧
      lam 𝓖 = 1 ∧ ∀ g : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
        ∫ w in 𝓕, g (e w) ∂ν = ∫ p in 𝓖, g p ∂lam := by
  first | exact @GlobalTheory.DarbouxMeasure.transport_covol_one | exact GlobalTheory.DarbouxMeasure.transport_covol_one | (intros; apply GlobalTheory.DarbouxMeasure.transport_covol_one <;> assumption)
end

