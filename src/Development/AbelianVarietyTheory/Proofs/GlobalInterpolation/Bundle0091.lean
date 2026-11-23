module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem finite_quot_divLat_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add (f := _), smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := GlobalTheory.exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  let f : Z →ₗ[𝓞 E] T := ev.restrict (p := Z) (q := T) fun x hx => hx
  let q : Z →ₗ[𝓞 E] _ :=
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD
  have hk : LinearMap.ker f ≤ LinearMap.ker q := by
    intro x hx
    have hxg : ∀ g : G, (x : HomE E a b) g = 0 := by
      intro g
      have h := congrFun (congrArg Subtype.val (LinearMap.mem_ker.mp hx)) g
      have h2 : (cA : E) • (x : HomE E a b) g = 0 := by
        rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
        exact h
      exact (smul_eq_zero.mp h2).resolve_left hA'
    have hxN : ∀ y ∈ N, (x : HomE E a b) y = 0 := by
      intro y hy
      rw [← hG] at hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact hxg ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => simp [hu, hv]
      | smul r u _ hu => simp [LinearMap.map_smul_of_tower, hu]
    have hxloc : ∀ (P : HeightOneSpectrum (𝓞 E)), ∀ y ∈ localization₂ P.asIdeal N, (x : HomE E a b) y = 0 := by
      intro P y hy
      obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
      have hs0 : (s : E) ≠ 0 := by
        intro h
        have : s = 0 := by exact_mod_cast h
        exact hs (this ▸ P.asIdeal.zero_mem)
      have h := hxN _ hsy
      rw [LinearMap.map_smul_of_tower] at h
      have h' : (s : E) • (x : HomE E a b) y = 0 := by
        exact h
      exact (smul_eq_zero.mp h').resolve_left hs0
    apply LinearMap.mem_ker.mpr
    change Submodule.Quotient.mk (Submodule.inclusion hZD x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (x : HomE E a b) ∈ mulLat cB (homAt S N N')
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x : HomE E a b), ?_, ?_⟩
    · rw [memH]
      intro P hP y hy
      simp [hxloc P y hy]
    · ext y
      simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, mul_inv_cancel₀ hB', one_smul]
  have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
  have : Module.Finite (𝓞 E) (LinearMap.range f) := Module.Finite.of_injective
    (LinearMap.range f).subtype Subtype.val_injective
  have : Module.Finite (𝓞 E) (Z ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  let q' := (LinearMap.ker f).liftQ q hk
  have hq' : Function.Surjective q' := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Submodule.Quotient.mk x, hx⟩
  have := Module.Finite.of_surjective q' hq' 
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩


end GlobalTheory.MomT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsStableOfTgtEq
section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ}

namespace PtModel

variable (M : PtModel X i)

theorem inc_eq_image (v : X.A.vT) (p : M.Pt) :
    {p₁ | M.Inc v p p₁} =
      (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) '' {q | (p.2 v).Inc q} := by
  ext p₁
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p₁.2 v, h3, ?_⟩
    refine Prod.ext h1.symm ?_
    funext v'
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Function.update_of_ne hv, h2 v' hv]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rfl, fun v' hv => by simp [Function.update_of_ne hv], ?_⟩
    simpa using hq

theorem update_pt_injective (v : X.A.vT) (p : M.Pt) :
    Function.Injective (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) := by
  intro q q' h
  have := congrArg (fun r : M.Pt => r.2 v) h
  simpa using this

theorem finsum_inc_eq (v : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, F p₁) =
      ∑ᶠ q ∈ {q | (p.2 v).Inc q}, F (p.1, Function.update p.2 v q) := by
  rw [inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]

theorem finite_inc_loc (v : X.A.vT) (p : M.Pt) : {q | (p.2 v).Inc q}.Finite := by
  have h := ((_root_.GlobalTheory.LvT.inc_finite_stable D u X i M v).1 p).1
  rw [inc_eq_image] at h
  exact Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn

theorem finsum_inc_comm (v v' : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v' p₁ p₂}, F p₂) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v' p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v p₁ p₂}, F p₂ := by
  by_cases hv : v = v'
  · subst hv; rfl
  have hv' : v' ≠ v := fun h => hv h.symm
  rw [finsum_inc_eq, finsum_inc_eq]
  simp only [finsum_inc_eq, Function.update_of_ne hv, Function.update_of_ne hv']
  rw [finsum_mem_comm _ (M.finite_inc_loc v p) (M.finite_inc_loc v' p)]
  simp only [Function.update_comm hv]

end PtModel

theorem formsStable_of_tgtEq : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → FormsStable X := by
  intro D u X Lv Kt hK
  refine ⟨fun i hi v φ hφ => ?_, fun i hi v v' φ hφ => ?_, fun i hi φ hφ => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i (Lv i hi) φ).1 hφ
    exact (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i (Lv i hi) _).2 ⟨_, _root_.GlobalTheory.LvT.uop_isExt D u X i (Lv i hi) v φ Φ hΦ⟩
  · obtain ⟨Φ, hΦ⟩ := (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i (Lv i hi) φ).1 hφ
    have h1 := _root_.GlobalTheory.LvT.uop_isExt D u X i (Lv i hi) v _ _ (_root_.GlobalTheory.LvT.uop_isExt D u X i (Lv i hi) v' φ Φ hΦ)
    have h2 := _root_.GlobalTheory.LvT.uop_isExt D u X i (Lv i hi) v' _ _ (_root_.GlobalTheory.LvT.uop_isExt D u X i (Lv i hi) v φ Φ hΦ)
    funext c
    rw [h1.1 c, h2.1 c]
    simp only []
    rw [(Lv i hi).finsum_inc_comm v v']
  · obtain ⟨Φ, hΦ⟩ := (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i (Lv i hi.le) φ).1 hφ
    exact (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X (i + 1) (Lv (i + 1) hi) _).2
      ⟨_, _root_.GlobalTheory.LvT.isExt_KT D u X i (Lv i hi.le) (Lv (i + 1) hi) (Kt i hi) φ Φ (hK i hi) hΦ⟩

end GlobalTheory.LvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLifts
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomGood

theorem inOK_iff_mem_OK (d : ℕ) (z : ℂ) : GlobalTheory.MomOne.InOK d z ↔ z ∈ JMB.OK d := Iff.rfl

theorem lamA_eq_lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : JMB.lamA lam x = lamC lam x := rfl

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  intro D cc δ N N' L L' g S e p _ lam N₀ n hd hLa y hy
  obtain ⟨-, -, hOK, hconj, -⟩ := GlobalTheory.MomDict.main D
  unfold GlobalTheory.MomT.goodLifts at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((κ : D.host.K) : D.host.E), ?_, ?_, e x, (hLa x).2 hx, ?_⟩
    · rw [hd]
      exact (inOK_iff_mem_OK _ _).1 ((hOK _).2 ⟨κ, rfl⟩)
    · rw [lamA_eq_lamC, ← hconj]
      exact hκ
    · exact map_smul e _ x
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.MomGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CocInt

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem hv_apply {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem emb_apply (x : HomE X.E a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    emb A x τ i j = A.δ * X.embC A.σ₀ τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (hX : X.Ok) (r : X.E) (x y : HomE X.E a b) :
    HV A.sc (emb A (r • x)) (emb A y) = HV A.sc (emb A x) (emb A (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [emb_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hX.conjE, Complex.conj_conj]
  ring

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add (embH _ _) x y

theorem coc_add_left (x y z : HomE X.E a b) : coc A (x + y) z = coc A x z + coc A y z := by
  simp only [coc, imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem coc_zero_left (z : HomE X.E a b) : coc A 0 z = 0 := by
  have := coc_add_left A 0 0 z
  rw [add_zero] at this
  linarith

theorem emb_injective (hX : X.Ok) (hδ : A.δ ≠ 0) : Function.Injective (emb A : HomE X.E a b → _) := by
  intro x y h
  obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [emb_apply, emb_apply] at this
  simpa using (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ this)

variable {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem emb_mem {x : HomE X.E a b} (hx : x ∈ per A N N') : emb A x ∈ LamC (X.embC A.σ₀) A.δ A.AA N N' :=
  ⟨x, hx, rfl⟩

theorem mem_per_iff (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') (x : HomE X.E a b) :
    x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n := by
  constructor
  · intro hx y hy
    have h1 := emb_mem A hx
    rw [← hL.1] at h1
    exact h1 _ (emb_mem A hy)
  · intro h
    have h1 : emb A x ∈ dualLat (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    rw [hL.1] at h1
    obtain ⟨x', hx', e⟩ := h1
    rwa [← emb_injective A hX hδ (a₁ := x') e]

theorem coc_int (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') {x y : HomE X.E a b}
    (hx : x ∈ per A N N') (hy : y ∈ per A N N') : ∃ n : ℤ, coc A x y = n := by
  obtain ⟨m, hm⟩ := (mem_per_iff A hX hδ hL x).1 hx y hy
  have h := hL.2.2 _ (emb_mem A hx) _ (emb_mem A hy)
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n + m, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (HV A.sc (emb A y) (emb A x)).re = (HV A.sc (emb A x) (emb A y)).re := by
    rw [hv_swap]; simp
  simp only [imH] at hm
  simp only [map_add (f := _), LinearMap.add_apply, Complex.add_re, h3, hm] at h2
  simp at h2
  simp only [coc, imH, hm]
  push_cast
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

theorem cocycle_integral : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  intro X A a b N N' hX hδ hL
  have h1 : ∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y) := by
    intro r x y
    simp only [coc, imH, altE, hv_smul A hX, and_self]
  refine ⟨h1, mem_per_iff A hX hδ hL, fun x y h => ?_⟩
  let I : Ideal (𝓞 X.E) :=
    { carrier := {r | ∀ s : 𝓞 X.E, ∃ n : ℤ, coc A ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [coc_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, coc_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 X.E) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField X.E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨v, hv, hy⟩ := (mem_locP _ _ _).1 hy
    have hmem : u * cO X.E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := coc_int A hX hδ hL (Submodule.smul_mem _ s hx) hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO X.E v)) • x = (star (algebraMap (𝓞 X.E) X.E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul X.E s, ← algebraMap_smul X.E u, ← algebraMap_smul X.E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, (h1 _ _ _).1, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hM.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 X.E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.MomT.CocInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HighestWeightVectorMemOfLtStableDualWeyl
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, rowW, rowDeg, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp [Pi.single_apply]

theorem hw_mem_of_lt : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → ∀ M M' : Submodule k (MvPolynomial (Fin N × Fin N) k), Good M → Good M' → M < M' → M' ≤ dualWeyl k N N ν → hw k le_rfl ν ∈ M' ∧ hw k le_rfl ν ∉ M := by
  intro p hp k _ _ N ν hν hal M M' hM hM' hlt hle
  have dom := _root_.GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl k N ν
  obtain ⟨μ, v, hμ, hvM', hvM, hvw, hraise⟩ := _root_.GlobalTheory.Alc.exists_dominant_highest_vector_of_lt k N M M' hM hM' hlt
    ⟨∑ a, ν a, fun f hf m hm => ((dom f (hle hf) m hm).2).le⟩
  have hv0 : v ≠ 0 := fun h => hvM (h ▸ zero_mem M)
  have hwt := _root_.GlobalTheory.Alc.rowE_rowWeight k N N μ v hvw
  have hrel := (_root_.GlobalTheory.Alc.rowOperators_main k N N).1
  have hhw := _root_.GlobalTheory.Alc.trace_pow_hw k _ N (rowE k N N) hrel M (fun a b f hf => hM.1 a b f hf)
    (fun a => (μ a : k)) v hraise (fun a => by rw [hwt.1 a, sub_self]; exact zero_mem M)
  have hval : ∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j := by
    intro j
    by_contra hne
    have h1 := hhw j
    have h2 : gel k N N j v = hcVal k (fun i => (ν i : k)) j • v := _root_.GlobalTheory.Alc.gel_dualWeyl_field k N ν hν j v (hle hvM')
    change gel k N N j v - _ ∈ M at h1
    rw [h2, ← sub_smul] at h1
    exact hvM ((Submodule.smul_mem_iff M (sub_ne_zero.mpr (Ne.symm hne))).mp h1)
  obtain ⟨m, hm⟩ : v.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
  have hmμ : ∀ a, μ a = rowDeg m a := fun a => by rw [← hvw (mem_support_iff.mp hm)]; exact (weight_rowW_apply m a)
  have hcond : ∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p := by
    intro h
    refine ⟨(hal h).1, ?_, (hal h).2⟩
    have hd := (dom v (hle hvM') m hm).1 1
    have hs : (Finset.univ.filter fun a : Fin N => a.val < 1) = {⟨0, h⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [hmμ]; exact hd
  have hμν : μ = ν := _root_.GlobalTheory.Alc.eq_of_hcVal_eq p hp k N ν μ hν hμ hcond hval
  subst hμν
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.Alc.hw_line_field k N μ hν v (hle hvM') hvw
  have hc0 : c ≠ 0 := by rintro rfl; exact hv0 (by rw [hc, zero_smul])
  refine ⟨?_, fun h => hvM (hc ▸ M.smul_mem c h)⟩
  have : hw k le_rfl μ = c⁻¹ • v := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]; exact M'.smul_mem _ hvM'

end GlobalTheory.Alc
end

