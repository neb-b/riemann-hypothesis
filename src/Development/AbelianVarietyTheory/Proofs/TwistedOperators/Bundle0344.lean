module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointMemCongruenceSubgroupOffPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongOff

open Matrix
open scoped TensorProduct

variable {D : D7}

theorem exists_F_mem_not_mem {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ S) :
    ∃ X : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) X ∈ 𝔪 ∧ X ∉ v.asIdeal := by
  classical
  have hsep : ∀ u ∈ S, ∃ x : 𝓞 D.host.F, x ∈ u.asIdeal ∧ x ∉ v.asIdeal := by
    intro u hu
    by_contra hn
    push_neg at hn
    have e : u.asIdeal = v.asIdeal := u.isMaximal.eq_of_le v.isPrime.ne_top hn
    exact hv (HeightOneSpectrum.ext e ▸ hu)
  choose! x hx hxv using hsep
  have hz : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ u ∈ S, x u) ∈ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪 (le_bot_iff.1 (h ▸ hJ))
    let Q : HeightOneSpectrum (𝓞 D.host.E) := ⟨J, hJp, hJ0⟩
    have hu := hS Q hJ
    have hxu : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (x (Q.under (𝓞 D.host.F))) ∈ J := hx _ hu
    rw [map_prod, ← Finset.prod_erase_mul _ _ hu]
    exact Ideal.mul_mem_left J _ hxu
  obtain ⟨K, hK⟩ := hz
  refine ⟨(∏ u ∈ S, x u) ^ K, by rwa [map_pow], fun h => ?_⟩
  have h1 := v.isPrime.mem_of_pow_mem K h
  obtain ⟨u, hu, h2⟩ := (v.isPrime.prod_mem_iff).1 h1
  exact hxv u hu h2

end GlobalTheory.CongOff

namespace GlobalTheory.CongOff
open Matrix
open scoped TensorProduct

section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem unit_int' {v : HeightOneSpectrum (𝓞 F)} {X : 𝓞 F} (hX : X ∉ v.asIdeal) :
    (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F ∧
    algebraMap F (v.adicCompletion F) (X : F) ≠ 0 := by
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) (X : F)) = 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v X
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hX] at this
    exact this
  refine ⟨?_, fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem latLoc_le_smul_of (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {v : HeightOneSpectrum (𝓞 F)}
    (X : 𝓞 F) (hX𝔪 : algebraMap (𝓞 F) (𝓞 E) X ∈ 𝔪) (hXv : X ∉ v.asIdeal) :
    GlobalTheory.AdelicU.latLoc F Λ v ≤ GlobalTheory.AdelicU.latLoc F (𝔪 • Λ) v := by
  obtain ⟨hint, hne⟩ := unit_int' hXv
  intro y hy
  refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _) (fun _ _ h h' => add_mem h h')
    (fun _ h => neg_mem h) hy
  have hm := Submodule.smul_mem_smul hX𝔪 hx
  have h3 : a * (algebraMap F (v.adicCompletion F) (X : F))⁻¹ ∈ v.adicCompletionIntegers F := mul_mem ha hint
  have h2 := GlobalTheory.AdelicU.tmul_mem_latLoc (F := F) h3 hm
  convert h2 using 1
  funext i
  have e : (algebraMap (𝓞 F) (𝓞 E) X • x) i = (X : F) • x i := by
    rw [Pi.smul_apply, Algebra.smul_def (X : F)]
    rfl
  rw [e, ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ hne, mul_one]
end General
end GlobalTheory.CongOff

namespace GlobalTheory.CongOff
open Matrix
open scoped TensorProduct

theorem fg_ideal_smul {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (N : Submodule R M) (hN : N.FG) : (I • N).FG := by
  have : Module.Finite R N := Module.Finite.iff_fg.2 hN
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  have h := (IsNoetherian.noetherian ((I • N).comap N.subtype))
  have e : ((I • N).comap N.subtype).map N.subtype = I • N :=
    Submodule.map_comap_eq_of_le (by rw [Submodule.range_subtype]; exact Submodule.smul_le_right)
  rw [← e]; exact h.map _

variable {D : D7}


set_option maxHeartbeats 1600000 in
theorem cong_fin {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (hS : ∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) (V : HSp D) (g : GA D V)
    (hoff : ∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v)
    (hon : ∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g = 1) :
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.AdelicU.frameLat V),
      (Lev.finE V g).1 *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • GlobalTheory.AdelicU.frameLat V) := by
  intro y hy
  obtain ⟨y', rfl⟩ : ∃ y' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) = y :=
    ⟨fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose, funext fun i => (GlobalTheory.LevSplit.swp_bij.2 (y i)).choose_spec⟩
  have hy' := (GlobalTheory.LevSplit.latHat_iff _ y').2 hy
  have e : (Lev.finE V g).1 *ᵥ (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) -
      (fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E (y' i)) =
      fun i => GlobalTheory.LevSplit.swp D.host.F D.host.E ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') i) := by
    funext i
    rw [Pi.sub_apply, Pi.sub_apply, map_sub]
    congr 1
    exact (RingHom.map_mulVec (GlobalTheory.LevSplit.swp D.host.F D.host.E) (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) y' i).symm
  rw [e, ← GlobalTheory.LevSplit.latHat_iff,
    GlobalTheory.AdelicU.mem_latHat_iff (fg_ideal_smul 𝔪 _ (GlobalTheory.AdelicU.frameLat_fg V))]
  intro v
  have hv := (GlobalTheory.AdelicU.mem_latHat_iff (GlobalTheory.AdelicU.frameLat_fg V) y').1 hy' v
  rw [show GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y' - y') =
      GlobalTheory.AdelicU.vecLoc v (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g *ᵥ y') - GlobalTheory.AdelicU.vecLoc v y' from
      funext fun i => map_sub _ _ _, GlobalTheory.AdelicU.vecLoc_mulVec]
  by_cases hvS : v ∈ S
  · rw [hon v hvS, map_one, Units.val_one, Matrix.one_mulVec, sub_self]; exact zero_mem _
  · obtain ⟨X, hX𝔪, hXv⟩ := exists_F_mem_not_mem h𝔪 hS hvS
    exact latLoc_le_smul_of _ 𝔪 X hX𝔪 hXv
      (sub_mem ((GlobalTheory.AdelicU.mem_stabLoc.1 (hoff v hvS) _).1 hv) hv)

end GlobalTheory.CongOff

namespace GlobalTheory.CongOff

theorem finE_mem_congLev_of_off : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ S) → ∀ k : GA D V, k ∈ GfC V → (∀ v ∉ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v) → (∀ v ∈ S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k = 1) → Lev.finE V k ∈ congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) 𝔪 := by
  intro D V S 𝔪 h𝔪 hS k _ hoff hon
  refine GlobalTheory.CongMember.mem_congLev_of D.sp.cm V.gram _ 𝔪 _ (GlobalTheory.LevSplit.finE_mem_UA V k)
    (cong_fin h𝔪 hS V k hoff hon) ?_
  rw [← map_inv]
  exact cong_fin h𝔪 hS V k⁻¹ (fun v hv => by rw [map_inv]; exact inv_mem (hoff v hv))
    (fun v hv => by rw [map_inv, hon v hv, inv_one])

end GlobalTheory.CongOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapNonvanishingConditionLocalise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LocCond

variable {D : D7}

theorem idAt_mul_idOff {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) :
    a * b = 0 := by
  have h1 := (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 ha
  have h2 := (GlobalTheory.FinPlLoc.mem_idOff_iff P b).1 hb
  calc a * b = (GlobalTheory.FinPlLoc.idem D P * a) * b := by rw [h1]
    _ = a * (GlobalTheory.FinPlLoc.idem D P * b) := by ring
    _ = 0 := by rw [h2, mul_zero]

theorem idOff_true_le {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idOff D (fun _ => True)) : a ∈ idOff D P := by
  unfold GlobalTheory.FinPl.idOff at *
  rw [Submodule.mem_iInf] at *
  intro w
  exact ha ⟨w.1, trivial⟩

theorem idAt_le_true {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D (fun _ => True) := by
  unfold GlobalTheory.FinPl.idAt at *
  obtain ⟨h0, -⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w => absurd trivial w.2⟩

theorem mul_mem_left' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hE i l)

theorem mul_mem_right' {I : Ideal (AE D)} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ I) : ∀ i j, (E ⬝ Z) i j ∈ I := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hZ l j)

theorem mul_eq_zero_of {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (E : Matrix (Fin m) (Fin n) (AE D))
    (Z : Matrix (Fin n) (Fin k) (AE D)) (hE : ∀ i j, E i j ∈ idOff D P) (hZ : ∀ i j, Z i j ∈ idAt D P) :
    E ⬝ Z = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idAt_mul_idOff (hZ l j) (hE i l)

theorem off_entries {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) :
    ∀ i j, (mt S g - 1) i j ∈ idOff D P := fun i j => by
  rw [Matrix.sub_apply]
  exact (GlobalTheory.FinPlLoc.mem_congGrp _ g).1 hg i j

theorem mt_off_mul {P : GlobalTheory.FinPl.Pl D → Prop} {S : HSp D} {g : GA D S} (hg : g ∈ grpOff S P) {k : ℕ}
    (Z : Matrix (Fin S.rank) (Fin k) (AE D)) (hZ : ∀ i j, Z i j ∈ idAt D P) : mt S g ⬝ Z = Z := by
  calc mt S g ⬝ Z = (mt S g - 1) ⬝ Z + Z := by rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
    _ = Z := by rw [mul_eq_zero_of _ _ (off_entries hg) hZ, zero_add]

end GlobalTheory.AscFin.LocCond


open GlobalTheory.AscFin.LocCond in
theorem GlobalTheory.AscFin.cond_loc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (P : GlobalTheory.FinPl.Pl D → Prop) (h₁ h₂ : GA D W), h₁ ∈ grpAt W P → h₂ ∈ grpOff W P → Cond dW p x y ψ (fun _ => True) (h₁ * h₂) → Cond dW p x y ψ P h₁ := by
  intro D ψ _ V V₀ W W₀ ρ σ dV dW p x y P h₁ h₂ _ h2 hc
  have e2 := off_entries (inv_mem h2)
  have hinv : mt W (h₁ * h₂)⁻¹ = mt W h₂⁻¹ ⬝ mt W h₁⁻¹ := by
    rw [_root_.mul_inv_rev, GlobalTheory.FinPlLoc.mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := hc.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have hk := idOff_true_le (P := P) (hoff i j)
    have hm := mul_mem_left' (mt W h₂⁻¹ - 1) (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) e2 i j
    have eq : mt W h₁⁻¹ ⬝ (x ⬝ u.1.1) - x - a =
        (mt W (h₁ * h₂)⁻¹ ⬝ (x ⬝ u.1.1) - x - a) - (mt W h₂⁻¹ - 1) ⬝ (mt W h₁⁻¹ ⬝ (x ⬝ u.1.1)) := by
      rw [hinv, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [eq, Matrix.sub_apply]
    exact sub_mem hk hm
  · intro N hN hlow hA
    refine hc.shift N (fun i j => idAt_le_true (hN i j)) hlow ?_
    have hZ : ∀ i j, (mt W h₁⁻¹ ⬝ (x ⬝ N)) i j ∈ idAt D P := mul_mem_right' _ _ (mul_mem_right' _ _ hN)
    rw [hinv, Matrix.mul_assoc, mt_off_mul (inv_mem h2) _ hZ]
    exact hA
  · intro ξ hξ ξ' hP heq
    refine hc.iso ξ hξ ξ' (fun i j => idAt_le_true (hP i j)) ?_
    have hZ : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D P := by
      rw [HypDec.incX_apply]
      exact mul_mem_right' _ _ hP
    rw [GlobalTheory.FinPlLoc.mt_mul, Matrix.mul_assoc, mt_off_mul h2 _ hZ]
    exact heq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionThetaMatrixCoeffRationalTranslat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.TranslateCoefInversion

variable {D : D7} {S T : HSp D}

theorem symplOH_neg_left' (x y : WO S T) : symplOH S T (-x) y = -symplOH S T x y := by
  obtain ⟨hl, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := hl x (-x) y
  rw [add_neg_cancel, GlobalTheory.ThetaSquare.symplOH_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem symplOH_skew' (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  obtain ⟨hl, hr, hs, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := hs (x + y)
  rw [hl, hr, hr, hs, hs, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem symplOH_neg_right' (x y : WO S T) : symplOH S T x (-y) = -symplOH S T x y := by
  rw [symplOH_skew', symplOH_neg_left', symplOH_skew' y x, neg_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) : star (ψ a) = ψ (-a) := by
  rw [GlobalTheory.ThetaAllChar.star_char hn, AddChar.inv_apply]

theorem chi_neg_neg (ψ : AddChar (AF D.host.F) ℂ) (γ x : WO S T) :
    GlobalTheory.ThetaAllChar.chi ψ S T (-γ) (-x) = GlobalTheory.ThetaAllChar.chi ψ S T γ x := by
  simp only [GlobalTheory.ThetaAllChar.chi, symplOH_neg_left', symplOH_neg_right', neg_neg]

theorem star_chi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (γ z : WO S T) :
    star (GlobalTheory.ThetaAllChar.chi ψ S T γ z) = GlobalTheory.ThetaAllChar.chi ψ S T (-γ) z := by
  simp only [GlobalTheory.ThetaAllChar.chi, star_psi hn, symplOH_neg_right', neg_add]

theorem rat_eq_zero_of_fin {x : WO S T} (hx : x ∈ ratL T S) (h0 : ∀ i j, finPart D (x i j) = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := hx
  ext i j
  have h : (1 : Af D.host.F) ⊗ₜ[D.host.F] m i j = 0 := h0 i j
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    let v : HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion D.host.F) = 1 := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
    exact zero_ne_one h2
  have e : m i j = 0 := by
    apply Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F (Af D.host.F)).injective
    rw [map_zero]
    exact h
  show incA D (m i j) = 0
  rw [e, map_zero]

theorem rat_eq_zero_of_inf {x : WO S T} (hx : x ∈ ratL T S) (h0 : ∀ i j, infPart D (x i j) = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := hx
  ext i j
  have h : (1 : Ainf D.host.F) ⊗ₜ[D.host.F] m i j = 0 := h0 i j
  have e : m i j = 0 := by
    apply Algebra.TensorProduct.includeRight_injective (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)
      (algebraMap D.host.F (Ainf D.host.F)).injective
    rw [map_zero]
    exact h
  show incA D (m i j) = 0
  rw [e, map_zero]


open GlobalTheory.ThetaAllChar in
theorem chiR_eq_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (γ : ratL T S)
    (h : ∀ x, chiR ψ S T γ x = 1) : γ = 0 := by
  have hall : ∀ c : AF D.host.F, (c • (γ : WO S T)) ∈ ratL T S := by
    intro c
    refine (chi_ker hψ _).1 fun δ => ?_
    have h1 := h ((-c) • (δ : WO S T))
    simp only [chiR, chi, GlobalTheory.FinTranslate.symplOH_smul_left] at h1 ⊢
    rw [symplOH_skew' (δ : WO S T) (γ : WO S T), mul_neg, ← neg_mul]
    exact h1
  have h1 : GlobalTheory.FinTranslate.eInf D • (γ : WO S T) = 0 :=
    rat_eq_zero_of_fin (hall _) fun i j => GlobalTheory.ThetaClosed.finPart_eInf_smul _
  have h2 : (1 - GlobalTheory.FinTranslate.eInf D) • (γ : WO S T) = 0 :=
    rat_eq_zero_of_inf (hall _) fun i j => GlobalTheory.ThetaClosed.infPart_one_sub_eInf_smul _
  have h3 : (γ : WO S T) = 0 := by
    rw [← one_smul (AF D.host.F) (γ : WO S T), ← add_sub_cancel (GlobalTheory.FinTranslate.eInf D) 1, add_smul, h1, h2, add_zero]
  exact Subtype.ext h3


open GlobalTheory.ThetaAllChar in
theorem sum_coef_mul_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → ∀ w x : WO S T, Summable (fun γ : ratL T S => ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖) → ∑' γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x = f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x := by
  intro D ψ hψ S T μ 𝓕 hc f f₀ hf hf₀ w x hs
  obtain ⟨hμ, h𝓕, h1⟩ := hc
  haveI := hμ
  obtain ⟨iG1, iG2, iG3, iG4, iG5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  obtain ⟨lc, lx, la, l0, ln, lker⟩ := chiR_laws (S := S) (T := T) hψ.1
  set g := heisO ψ S T w f₀ with hgdef
  have hg : IsThetaFunO ψ S T g := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 w f₀ hf₀

  have hb : ∀ γ : ratL T S, heisO ψ S T ((γ : WO S T) + w) f₀ =
      fun y => ψ (-(symplOH S T γ w)) * (chi ψ S T γ y * g y) := by
    intro γ
    have e1 := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).2.1 γ w f₀
    rw [heisO_rat γ.2 hg] at e1
    funext y
    have e2 := congrFun e1 y
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e2
    rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  set F : WO S T → ℂ := fun z => f z * star (g z) with hFdef
  have hFc : Continuous F := hf.cont.mul hg.cont.star
  have hFp : ∀ γ ∈ ratL T S, ∀ z, F (γ + z) = F z :=
    GlobalTheory.ThetaAllChar.periodic_of_one (GlobalTheory.ThetaAllChar.isTheta_mul_star hn hf hg)
  have hχp : ∀ (a : ratL T S), ∀ γ ∈ ratL T S, ∀ z, chiR ψ S T a (γ + z) = chiR ψ S T a z := fun a =>
    GlobalTheory.ThetaAllChar.periodic_of_one (GlobalTheory.ThetaAllChar.isTheta_chi hψ.1 a.2)
  set Φ : WO S T → ℂ := fun z => F (z + x) with hΦdef
  set I : ratL T S → ℂ := fun γ => ∫ z in 𝓕, chiR ψ S T (-γ) z * F z ∂μ with hIdef
  set J : ratL T S → ℂ := fun a => ∫ z in 𝓕, chiR ψ S T a z * Φ z ∂μ with hJdef
  have hcoef : ∀ γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) = ψ (symplOH S T γ w) * I γ := by
    intro γ
    rw [thPair, hb γ, hIdef, ← integral_const_mul]
    congr 1
    funext a
    simp only [hFdef, chiR]
    rw [star_mul, star_mul, star_psi hn, neg_neg, star_chi hn]
    simp only [AddSubgroup.coe_neg]
    ring
  have hJ : ∀ γ : ratL T S, J (-γ) = chi ψ S T γ x * I γ := by
    intro γ
    have e := GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) μ 𝓕 h𝓕
      (fun z => chiR ψ S T (-γ) (z + -x) * F z)
      (fun γ' hγ' z => by simp only [add_assoc, hχp _ γ' hγ', hFp γ' hγ']) x
    simp only [add_neg_cancel_right] at e
    simp only [hJdef, hΦdef, hIdef]
    rw [e, ← integral_const_mul]
    congr 1
    funext z
    rw [lx, show chiR ψ S T (-γ) (-x) = chi ψ S T γ x by simp only [chiR, AddSubgroup.coe_neg]; exact chi_neg_neg ψ _ _]
    ring
  have hkey : ∀ γ : ratL T S, thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀) * heisO ψ S T ((γ : WO S T) + w) f₀ x =
      g x * J (-γ) := by
    intro γ
    have hp1 : ψ (symplOH S T γ w) * ψ (-(symplOH S T γ w)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hcoef, hb γ, hJ]
    linear_combination (I γ * chi ψ S T γ x * g x) * hp1
  have hnorm : ∀ γ : ratL T S, ‖J (-γ)‖ = ‖thPair μ 𝓕 f (heisO ψ S T ((γ : WO S T) + w) f₀)‖ := by
    intro γ
    rw [hJ, hcoef, norm_mul, norm_mul, hn, GlobalTheory.ThetaAllChar.norm_chi hn]
  have hsJ : Summable J := by
    have h2 : Summable fun γ : ratL T S => J (-γ) := by
      refine Summable.of_norm ?_
      simp only [hnorm]
      exact hs
    exact (Equiv.neg (ratL T S)).summable_iff.1 h2
  have hinv := GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero (WO S T) (ratL T S) K hK hcov
    (ratL T S) (chiR ψ S T) lc lx la l0 ln lker (fun a ha => chiR_eq_zero hψ.1 a ha) μ 𝓕 hμ h𝓕 h1 Φ
    (hFc.comp (continuous_id.add continuous_const)) (fun γ hγ z => by simp only [hΦdef, add_assoc, hFp γ hγ]) hsJ
  simp only [hkey]
  have hre : ∑' γ : ratL T S, J (-γ) = ∑' a, J a := by
    have e := (Equiv.neg (ratL T S)).tsum_eq J
    simp only [Equiv.neg_apply] at e
    exact e
  rw [tsum_mul_left, hre, show (∑' a, J a) = Φ 0 from hinv]
  simp only [hΦdef, hFdef, zero_add]
  ring

end GlobalTheory.TranslateCoefInversion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumTwistSubOneSupportedAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TwistBlockK

theorem atK_sub_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  intro F E _ _ _ _ _ d v g Y hg hY u hu
  have hgu := hg u hu
  have hYu : u • Y = 0 := hY u hu
  rw [smul_sub, sub_eq_zero] at hgu
  have h11 : u • g.toBlocks₁₁ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have h22 : u • g.toBlocks₂₂ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using this
  have h12 : u • g.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.one_apply] using this
  have h21 : u • g.toBlocks₂₁ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.one_apply] using this
  rw [smul_sub, smul_add, ← Matrix.smul_mul, hYu, Matrix.zero_mul, add_zero,
    smul_comm u (⅟(2 : AF F))]
  simp only [smul_add, h11, h12, h21, h22, add_zero]
  rw [← add_smul, invOf_two_add_invOf_two, one_smul, sub_self]

end GlobalTheory.TwistBlockK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIdealSmulAdelicPointRationalLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_ideal_smul_adelicPointRationalLattice : ∀ (D : D7) (V : HSp D) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (x : GA D V) (y : Fin V.rank → D.host.E), (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) → y ∈ 𝔪 • latAt Λ x := by
  first | exact @GlobalTheory.SepLatIdeal.mem_smul_latAt | exact GlobalTheory.SepLatIdeal.mem_smul_latAt | (intros; apply GlobalTheory.SepLatIdeal.mem_smul_latAt <;> assumption)
end

