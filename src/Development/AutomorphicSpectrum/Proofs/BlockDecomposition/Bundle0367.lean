module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VoganMinimalTypeStatement
section
namespace GlobalTheory.CompanionTheory.DiscreteSeries

private lemma two_mul_rhoN_add_rhoC_eq_card_sub_card {n : ℕ} (ε : Fin n → Bool) (x : Fin n) :
    2 * (Formalism.REAL.rhoN ε x + Formalism.REAL.rhoC ε x) =
      (({y | x < y} : Finset (Fin n)).card : ℝ) - (({y | y < x} : Finset (Fin n)).card : ℝ) := by
  have hA : ({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card = ({y | x < y} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : x < y <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hB : ({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card
      + ({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card = ({y | y < x} : Finset (Fin n)).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h : y < x <;> by_cases h' : ε y = ε x <;> simp [h, h']
  have hA' : (({y | x < y ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | x < y ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | x < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hA
  have hB' : (({y | y < x ∧ ε y ≠ ε x} : Finset (Fin n)).card : ℝ)
      + (({y | y < x ∧ ε y = ε x} : Finset (Fin n)).card : ℝ)
      = (({y | y < x} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast hB
  simp only [Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  linarith

private lemma rhoN_add_rhoC_le_of_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) :
    Formalism.REAL.rhoN ε b + Formalism.REAL.rhoC ε b ≤ Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a := by
  have h1 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε a
  have h2 := two_mul_rhoN_add_rhoC_eq_card_sub_card ε b
  have c1 : ({y | b < y} : Finset (Fin n)).card ≤ ({y | a < y} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hab hy
  have c2 : ({y | y < a} : Finset (Fin n)).card ≤ ({y | y < b} : Finset (Fin n)).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact lt_trans hy hab
  have c1' : (({y | b < y} : Finset (Fin n)).card : ℝ) ≤ (({y | a < y} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c1
  have c2' : (({y | y < a} : Finset (Fin n)).card : ℝ) ≤ (({y | y < b} : Finset (Fin n)).card : ℝ) := by
    exact_mod_cast c2
  linarith

private lemma nsq_le_nsq_add_of_dot_nonneg {n : ℕ} (v w : Fin n → ℝ) (h : 0 ≤ Formalism.REAL.dot v w) :
    Formalism.REAL.nsq v ≤ Formalism.REAL.nsq (v + w) := by
  unfold Formalism.REAL.nsq Formalism.REAL.dot at *
  have h2 : 0 ≤ ∑ a, w a * w a := Finset.sum_nonneg (fun a _ => mul_self_nonneg (w a))
  have e : ∑ a, (v + w) a * (v + w) a = ∑ a, v a * v a + 2 * ∑ a, v a * w a + ∑ a, w a * w a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by simp only [Pi.add_apply]; ring)
  rw [e]
  linarith

private lemma dot_nonneg_sum_root_of_antitone {n : ℕ} (v : Fin n → ℝ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b : Fin n, c a b ≠ 0 → a < b) (hmono : ∀ a b : Fin n, a < b → v b ≤ v a) :
    0 ≤ Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) := by
  have hdot : Formalism.REAL.dot v (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b)
      = ∑ a, ∑ b, (c a b : ℝ) * (v a - v b) := by
    unfold Formalism.REAL.dot
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hdot]
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  by_cases h0 : c a b = 0
  · simp [h0]
  · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hmono a b (hc a b h0)))


open GlobalTheory.LowestKTypeDetermines in
theorem stepVogan : PositivityTheory.RgDs.Hilb.StepVogan := by
  intro n ε lam η hlam hη
  obtain ⟨c, hc, rfl⟩ := hη
  have hk : ReciprocityTheory.ChartRestriction.DS.lowK ε lam = Formalism.QuantumDeterminants.lowK ε lam := by rfl
  unfold Formalism.MainNotions.S.vNormSq
  rw [hk, add_right_comm]
  apply nsq_le_nsq_add_of_dot_nonneg
  apply dot_nonneg_sum_root_of_antitone _ c hc
  intro a b hab
  simp only [Formalism.QuantumDeterminants.lowK, two_nsmul, two_smul, Pi.add_apply, Pi.sub_apply]
  have h1 := rhoN_add_rhoC_le_of_lt ε hab
  have h2 := hlam.1 hab
  linarith

end GlobalTheory.CompanionTheory.DiscreteSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorsSpanDense
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgDsHilb

open ReciprocityTheory.ChartRestriction.DS

theorem stepWtSpan : PositivityTheory.RgDs.Hilb.StepWtSpan := by
  intro n ε S hSf hSD hSK N _ _ e he
  classical
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hE : IsGlRep (smE ε (rreg ε)) := hD.glRep
  have hKU : IsKUnitary ε (smE ε (rreg ε)) :=
    isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, rreg ε k x ∈ S := hSK
  haveI := hSf
  haveI hS'f : FiniteDimensional ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hS'k : IsKStableSub ε (smE ε (rreg ε)) (S.comap (smD ε (rreg ε)).subtype) :=
    isKStableSub_of_kStable hσ hD _ hS'f fun k hk v hv =>
      ⟨⟨rreg ε k v, hD.kStable k hk _ v.2⟩, hSK' k hk _ hv, rfl⟩
  let T : Fin n → Module.End ℂ (S.comap (smD ε (rreg ε)).subtype) :=
    fun c => (smE ε (rreg ε) c c).restrict (hS'k c c rfl)
  have hTs : ∀ c, (T c).IsSymmetric := fun c x z => hKU c c rfl (x : smD ε (rreg ε)) (z : smD ε (rreg ε))
  have hcomm : Pairwise (Function.onFun Commute T) := fun a c _ =>
    LinearMap.ext fun x => Subtype.ext (kUnit_diag_comm hE a c (x : smD ε (rreg ε)))
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hTs hcomm
  let e' : (S.comap (smD ε (rreg ε)).subtype) →ₗ[ℂ] N :=
    e.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap
  by_contra hno
  push_neg at hno
  have hle : ∀ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (T c) (χ c)) ≤ LinearMap.ker e' := by
    intro χ x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hxc : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) = χ c • (x : smD ε (rreg ε)) := fun c =>
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx c))
    have hx0' : (x : smD ε (rreg ε)) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxν : ∀ c, smE ε (rreg ε) c c (x : smD ε (rreg ε)) =
        (((χ c).re : ℝ) : ℂ) • (x : smD ε (rreg ε)) := fun c =>
      (hxc c).trans (congrArg (· • (x : smD ε (rreg ε))) (kUnit_eig_real hKU hx0' (hxc c)))
    exact hno (fun c => (χ c).re) (Submodule.comapSubtypeEquivOfLe hSD x)
      ((isWtOn_iff hσ hD (x : smD ε (rreg ε)) _).2 hxν)
  have hker : LinearMap.ker e' = ⊤ := top_le_iff.mp (htop ▸ iSup_le hle)
  refine he (LinearMap.ext fun y => ?_)
  have hy : (Submodule.comapSubtypeEquivOfLe hSD).symm y ∈ LinearMap.ker e' := hker ▸ Submodule.mem_top
  have h2 : e' ((Submodule.comapSubtypeEquivOfLe hSD).symm y) = 0 := hy
  calc e y = e (Submodule.comapSubtypeEquivOfLe hSD ((Submodule.comapSubtypeEquivOfLe hSD).symm y)) := by
        rw [LinearEquiv.apply_symm_apply]
    _ = 0 := h2

end GlobalTheory.CompanionTheory.RgDsHilb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijective
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ρ : O →+* k}

def polyV {m : ℕ} {𝒱 : Set X.Opens} (P : Poly (sP (stF q ρ m 𝒱))) : Poly (sV q ρ m 𝒱) where
  P := P.P
  j := P.j
  X := P.X
  X_mem := P.X_mem
  univ := P.univ
  span := P.span

def frameV {m : ℕ} {𝒱 : Set X.Opens} {d : ℕ} (E : Frame (sP (stF q ρ m 𝒱)) d) : Frame (sV q ρ m 𝒱) d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

theorem nil_m (k : Type) [Field k] [CharP k l] [PerfectRing k l] (m : ℕ) : IsNilpotent ((l : ℕ) : Wc.Wm l k m) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

theorem o_bij {n : ℕ} (hn : n ≠ 0) (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory) :
    Function.Bijective (((mqS q ρ hn 𝒱).o (IdF.span _ ((l : WittVector l k) ^ n)) fun _ => le_rfl).τ T) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show T.obj.B ⧸ lI n T.obj from x)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (show T.obj.B ⧸ lI n T.obj from y)
    exact congrArg Subtype.val hxy
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk (lI n T.obj) a, Subtype.ext rfl⟩

theorem iso_bij {m : ℕ} {T T' : Thick (Wc.L l (B.schFn q) ρ m)} (e : T ≅ T') : Function.Bijective e.hom.φ := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.φ, fun x => ?_, fun x => ?_⟩
  · exact RingHom.congr_fun (congrArg (fun f => f.φ) e.hom_inv_id) x
  · exact RingHom.congr_fun (congrArg (fun f => f.φ) e.inv_hom_id) x


set_option maxHeartbeats 1000000 in
theorem local_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ}
    (cW : Coord q W d) (j : ℕ) :
    Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨c', hF', -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart (Wc.pd l k (n + 1)) l hl0 (nil_m k (n + 1)) q
    ((Wc.res l k (n + 1)).comp ρ) cW
  obtain ⟨c, e, hec, hfl⟩ := GlobalTheory.T.witt_chart_descend_level q ρ hn c'
  have hF : FlatT c.D := hfl (GlobalTheory.T.flat_thickening_quotient l k O (B.schFn q) ρ n hn c'.D hF')
  obtain ⟨PA, hPA⟩ := poly_all (Wc.pd l k n) l hl0 q ((Wc.res l k n).comp ρ) FlatT (Or.inr rfl) {W}
  obtain ⟨PB, hPB⟩ := poly_all (Wc.pd l k (n + 1)) l hl0 q ((Wc.res l k (n + 1)).comp ρ) FlatT (Or.inr rfl) {W}
  have hgA := GlobalTheory.CompanionTheory.ChartMaps.good c
  have hgB := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQA : ∀ T, stF q ρ n {W} T → InU W T := by
    rintro T ⟨-, V, rfl, hV⟩
    exact hV
  have hQB : ∀ T, stF q ρ (n + 1) {W} T → InU W T := by
    rintro T ⟨-, V, rfl, hV⟩
    exact hV
  have hDA : stF q ρ n {W} c.D := ⟨hF, W, rfl, c.inV⟩
  have hDB : stF q ρ (n + 1) {W} c'.D := ⟨hF', W, rfl, c'.inV⟩
  let E : Frame (sV q ρ n {W}) d := frameV (c.frame hgA _ hQA hDA)
  let E' : Frame (sV q ρ (n + 1) {W}) d := frameV (c'.frame hgB _ hQB hDB)
  let M := mqS q ρ hn {W}
  let e' : E.D ⟶ M.G.obj E'.D := ObjectProperty.homMk e.hom
  have he : M.Fr E E' e' := by
    intro i T s₁ s₂
    change M.ρ T (qφ s₂.hom (e.hom.φ (c.t i)) - qφ s₁.hom (e.hom.φ (c.t i))) =
      Ideal.Quotient.mk _ (s₂.hom.φ (c'.t i) - s₁.hom.φ (c'.t i))
    rw [hec]
    rfl
  let b : ℤ → IdF (sV q ρ (n + 1) {W}).A := fun _ => IdF.span _ ((l : WittVector l k) ^ n)
  exact GlobalTheory.CompanionTheory.LocCmp.localComparison M (polyV PA) (polyV PB) E E' e' he b (fun _ _ => le_rfl) 0 (hPA 0).2.1
    (fun r _ => ((hPB r).2.2 (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n))).2.2)
    (fun r' _ _ => (o_bij hn {W} E'.D).comp (iso_bij e)) j

end GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal

end
end

