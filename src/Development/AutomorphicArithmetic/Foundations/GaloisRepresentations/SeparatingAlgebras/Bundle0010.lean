module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FrameW
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem cAll_fin' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {c : UA E n}
    (hc : c ∈ finU (E := E) (n := n)) : cAll c = 1 := by
  funext v
  have : cInf c = 1 := hc
  simp [cAll, cEmb, this]

theorem UpperTheory.Gal.Gen.frameW_pf :
    UpperTheory.Gal.Gen.Kappa → UpperTheory.Gal.Gen.DenomBdd → UpperTheory.Gal.Gen.RhoBound → UpperTheory.Gal.Gen.LatFacts → UpperTheory.Gal.Gen.LevelEx → UpperTheory.Gal.Gen.FrameW := by
  intro hK hD hR hL hE E _ _ _ l _ ι a W J t ht
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨κ, hκr, hκi, hκd⟩ := hK E l ι a
  let ρ := Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W
  let M : UA E a → (InfinitePlace E → GL (Fin a) ℂ) := fun g => (cAll g)⁻¹ * κ g
  let b : UA E a → {x : W.Sp // CoefLe ι 1 x.1} → W.Sp := fun g x => ρ (M g) x.1
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hpow : ∀ d : ℕ, (1 : ℝ) ≤ (l : ℝ) ^ d := fun d => one_le_pow₀ hl1
  have hgrow : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c) x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c) _ (hpow d) (fun τ i j => hκd c d hc τ i j) x hx
  have hgrowInv : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c)⁻¹ x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c)⁻¹ _ (hpow d) (fun τ i j => by
      have h := hκd c d hc τ i j
      simp only [Pi.inv_apply, inv_inv]
      exact ⟨h.2, h.1⟩) x hx
  have hval : ∀ f : algForms W, ∀ γ ∈ ratU E a, ∀ s x, x ∈ infU E a → ∀ c : finU (E := E) (n := a),
      (∀ v g, f.1 v (g * (c : UA E a)) = f.1 v g) → ∀ v,
      f.1 (ρ (M (γ * s * x * c)) v) (γ * s * x * c) = f.1 (ρ (M s) (ρ (κ (c : UA E a)) v)) s := by
    intro f γ hγ s x hx c hf v
    have hM : cAll x * M (γ * s * x * c) = M s * κ (c : UA E a) := by
      simp only [M, map_mul, hκr γ hγ, hκi x hx, cAll_fin' c.2, mul_one]
      group
    have hA : ∀ v, f.1 v (γ * s * x * c) = f.1 v (s * c * x) := by
      intro v
      rw [mul_assoc γ s, mul_assoc γ, (f.2.1 v).left γ hγ, mul_assoc s x, ← fin_mul_inf c.2 hx, ← mul_assoc]
    have hB : ∀ v, f.1 v (s * c * x) = f.1 (W.rep ⟨x, hx⟩ v) (s * c) := by
      intro v
      rw [f.2.2 ⟨x, hx⟩ v]
      rfl
    have e3 : W.rep ⟨x, hx⟩ (ρ (M (γ * s * x * c)) v) = ρ (M s) (ρ (κ (c : UA E a)) v) := by
      change ρ (cAll x) (ρ (M _) v) = _
      rw [← Module.End.mul_apply, ← map_mul, hM, map_mul, Module.End.mul_apply]
    rw [hA, hB, hf, e3]
  refine ⟨{x : W.Sp // CoefLe ι 1 x.1}, b, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨C, hC, hfC⟩ := hE E a W f
    obtain ⟨d, hd⟩ := hD E l hlp a C hC.compact
    let C₃ : Subgroup (finU (E := E) (n := a)) := C.subgroupOf (finU (E := E) (n := a))
    have hC₃o : IsOpen (C₃ : Set (finU (E := E) (n := a))) := by
      obtain ⟨N, hNo, hN1, hNC⟩ := hC.isOpen
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
        (Filter.mem_of_superset ((hNo.preimage continuous_subtype_val).mem_nhds hN1) ?_)
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, x.2⟩)
    obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a C₃ hC₃o
    let φ : UA E a → (W.Sp →ₗ[ℂ] ℂ) := fun s => (LinearMap.proj s) ∘ₗ f.1 ∘ₗ (ρ (M s))
    have hφ : ∀ s, ∃ m : ℝ, 0 ≤ m ∧ ∀ (R : ℝ) (x : W.Sp), CoefLe ι R x.1 → ‖ι.symm (φ s x)‖ ≤ m * R :=
      fun s => (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).1 (φ s)
    choose m hm0 hm using hφ
    refine ⟨(∑ s ∈ S, m s) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at), fun g i => ?_⟩
    obtain ⟨γ, hγ, s, hs, y, hy, c, hc, rfl⟩ := hS g
    have hcC : (c : UA E a) ∈ C := Subgroup.mem_subgroupOf.1 hc
    have e := hval f γ hγ s y hy c (fun v g => hfC _ hcC v g) i.1
    have hb : f.1 (b (γ * s * y * c) i) (γ * s * y * c) = φ s (ρ (κ (c : UA E a)) i.1) := e
    rw [hb]
    refine (hm s _ _ (hgrow _ d (hd _ hcC) i.1 i.2)).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hm0 q) hs) (by positivity)
  · intro f h0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    funext g
    obtain ⟨c, hc0, hc⟩ := (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).2 (ρ (M g)⁻¹ v)
    have h1 := h0 g ⟨c • ρ (M g)⁻¹ v, hc⟩
    have h2 : b g ⟨c • ρ (M g)⁻¹ v, hc⟩ = c • v := by
      change ρ (M g) (c • ρ (M g)⁻¹ v) = c • v
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h2, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · intro F R hF j g i
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hF g i)
    have e : opOf (RU E a) (t j) (F (b g i)) g = ∑ h ∈ (t j).support, t j h * F (b g i) (g * h) := by
      simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun h hh => ?_
    obtain ⟨hfin, d, hd, hn⟩ := ht j h hh
    have hMh : M g = M (g * h) * (κ h)⁻¹ := by
      simp only [M, map_mul, cAll_fin' hfin, mul_one]
      group
    set y : W.Sp := ρ (κ h)⁻¹ i.1 with hy
    have hyc := hgrowInv h d hd i.1 i.2
    have hx : CoefLe ι 1 ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
      intro q
      have hq := hyc q
      have e1 : AddMonoidAlgebra.coeff ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) q =
          t j h * AddMonoidAlgebra.coeff (y : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) q := by
        simp [MvPolynomial.coeff_smul]
      rw [e1, map_mul, norm_mul]
      have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
      calc _ ≤ ((l : ℝ)⁻¹) ^ (a * d * GlobalTheory.CongW.wtSize W.at) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at) :=
            mul_le_mul hn hq (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [← pow_mul, inv_pow, show d * (a * GlobalTheory.CongW.wtSize W.at) = a * d * GlobalTheory.CongW.wtSize W.at by ring]
            exact inv_mul_cancel₀ (by positivity)
    have hb : t j h * F (b g i) (g * h) = F (b (g * h) ⟨t j h • y, hx⟩) (g * h) := by
      have : b g i = ρ (M (g * h)) y := by
        change ρ (M g) i.1 = _
        rw [hMh, map_mul, Module.End.mul_apply]
      change _ = F (ρ (M (g * h)) (t j h • y)) (g * h)
      rw [this, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hb]
    exact hF _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LatFacts
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.latFacts_pf :
    UpperTheory.Gal.Gen.LatFacts := by
  classical
  intro l _ ι σ V _
  refine ⟨fun φ => ?_, fun x => ?_⟩
  · let B := Module.finBasis ℂ V
    open MvPolynomial in
    have h : ∀ i, ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
        B.repr v i = ∑ m : s, a m * AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 := by
      intro i
      classical
      let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
      let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
      have hR : LinearMap.ker R = ⊥ := by
        refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
        have h0 : ∀ m : s, AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 = 0 := fun m => congrFun hv m
        refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
        by_cases hm : m ∈ s
        · simpa using h0 ⟨m, hm⟩
        · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
            calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
              _ = _ := by rw [Submodule.coe_sum]; rfl
          rw [hv', coeff_sum]
          simp only [coeff_smul, ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
          refine Finset.sum_eq_zero fun j _ => ?_
          have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
            hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
          rw [notMem_support_iff.1 this, smul_zero]
      obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
      refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
      have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
        rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
      rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [hs, smul_eq_mul, mul_comm]
      rfl
    choose s a ha using h
    refine ⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun R x hx => ?_⟩
    have e : φ x = ∑ i, B.repr x i * φ (B i) := by
      have h := congrArg φ (B.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha i x, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul, Finset.sum_mul]
    calc _ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R * ‖ι.symm (φ (B i))‖ :=
          mul_le_mul_of_nonneg_right (h1 i) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  · have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith)
    set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ + 1 with hTdef
    have hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    have hT : 0 < T := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)
    have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    refine ⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩
    have hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [map_natCast, Padic.norm_p] at h
      exact h
    have hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
      rw [map_pow, map_natCast, norm_pow, hnl]
    have hc : ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ ≤ T := by
      by_cases hm : m ∈ x.1.support
      · have := Finset.single_le_sum (f := fun m => ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖)
          (fun m _ => norm_nonneg _) hm
        linarith
      · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]
        exact hT.le
    have e : AddMonoidAlgebra.coeff (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) m =
        (l : ℂ) ^ k * AddMonoidAlgebra.coeff x.1 m := by
      rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [e, map_mul, norm_mul, hn]
    calc _ ≤ ((l : ℝ)⁻¹) ^ k * T := mul_le_mul_of_nonneg_left hc (pow_nonneg hl0.le _)
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right hk.le hT.le
      _ = 1 := inv_mul_cancel₀ hT.ne'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocRho
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.Loc

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

theorem coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

theorem coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

theorem coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

theorem coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

theorem coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

end CoefLeLemmas

theorem norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh58.norm_det_le ι M R hR h

def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz
  simp only [DomWeight.dual, Int.natAbs_neg]
  exact Equiv.sum_comp Fin.revPerm (fun k => (lam.w k).natAbs)

theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  cases a with
  | zero => simp
  | succ n =>
    have hd : lam.detShift = lam.w (Fin.last n) := by
      simp [DomWeight.detShift, Fin.last]
    have hl : lam.natW (Fin.last n) = 0 := by
      simp [DomWeight.natW, hd]
    have hi : ∀ i : Fin n, lam.natW i.castSucc ≤ (lam.w i.castSucc).natAbs + (lam.w (Fin.last n)).natAbs := by
      intro i
      simp only [DomWeight.natW, hd]
      omega
    have h1 : ∑ i : Fin n, lam.natW i.castSucc ≤
        (∑ i : Fin n, (lam.w i.castSucc).natAbs) + n * (lam.w (Fin.last n)).natAbs := by
      calc ∑ i : Fin n, lam.natW i.castSucc
          ≤ ∑ i : Fin n, ((lam.w i.castSucc).natAbs + (lam.w (Fin.last n)).natAbs) :=
            Finset.sum_le_sum fun i _ => hi i
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc, hl, hd]
    unfold sz
    rw [Fin.sum_univ_castSucc]
    generalize (∑ i : Fin n, (lam.w i.castSucc).natAbs) = t at h1 ⊢
    generalize (lam.w (Fin.last n)).natAbs = e at h1 ⊢
    generalize (∑ i : Fin n, lam.natW i.castSucc) = u at h1 ⊢
    nlinarith [Nat.zero_le (n * t), Nat.zero_le (n * e)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp only [emb]
  rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem emb_injective : Function.Injective (emb (E := E)) := by
  rintro (v | v) (w | w) h
  · have := congrArg InfinitePlace.mk h
    rw [mk_emb_inl, mk_emb_inl] at this
    rw [this]
  · exfalso
    have := congrArg InfinitePlace.mk h
    rw [mk_emb_inl, mk_emb_inr] at this
    subst this
    exact conjugate_ne v.embedding h.symm
  · exfalso
    have := congrArg InfinitePlace.mk h
    rw [mk_emb_inr, mk_emb_inl] at this
    subst this
    exact conjugate_ne v.embedding h
  · have := congrArg InfinitePlace.mk h
    rw [mk_emb_inr, mk_emb_inr] at this
    rw [this]

def wI {T : Type} [DecidableEq T] (I : Finset T) (n : ℕ) : T × Fin n × Fin n → ℕ := fun v => if v.1 ∈ I then 1 else 0

theorem homog_of_mem {T : Type} [Fintype T] [DecidableEq T] (I : Finset T) (n : ℕ) (lam : T → DomWeight n)
    (x : MvPolynomial (T × Fin n × Fin n) ℂ) (hx : x ∈ Formalism.L2.DIV.VV ℂ lam) :
    MvPolynomial.IsWeightedHomogeneous (wI I n) x (∑ τ, if τ ∈ I then ∑ i, (lam τ).natW i else 0) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hx
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨F, hF, rfl⟩
  refine (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).2 ?_
  refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun τ _ => ?_
  intro d hd
  obtain ⟨m, rfl, hm⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ hd
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = (lam τ).natW :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (hF τ).1 hm
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
  by_cases hτ : τ ∈ I
  · rw [if_pos hτ, ← hw, Finsupp.weight_apply]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul, wI, if_pos hτ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply]
  · simp [wI, hτ, Finsupp.sum]

theorem block_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] (I : Finset T) {n : ℕ}
    (A : T → Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R) (hA : ∀ τ i j, ‖ι.symm (A τ i j)‖ ≤ if τ ∈ I then R else 1)
    (D : ℕ) (x : MvPolynomial (T × Fin n × Fin n) ℂ) (hx : MvPolynomial.IsWeightedHomogeneous (wI I n) x D)
    (h1 : CoefLe ι 1 x) : CoefLe ι (R ^ D) (Formalism.GradedWeylDivisibility.blockAct ℂ A x) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hr : ∀ τ, (if τ ∈ I then R else 1) = R ^ (if τ ∈ I then 1 else 0) := fun τ => by split_ifs <;> simp
  have hy : ∀ v, CoefLe ι (R ^ wI I n v) (y v) := fun v =>
    coefLe_sum ι _ _ (pow_nonneg hR0 _) fun b _ => coefLe_C_mul_X ι (one_le_pow₀ hR) ((hA _ _ _).trans_eq (hr _)) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (AddMonoidAlgebra.coeff x m) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : Finsupp.weight (wI I n) m = D := hx (MvPolynomial.mem_support_iff.1 hm)
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => (R ^ wI I n v) ^ m v)
    (fun _ => by positivity) (fun v _ => coefLe_pow ι (pow_nonneg hR0 _) (hy v) (m v))
  have e2 : ∏ v ∈ m.support, (R ^ wI I n v) ^ m v = R ^ D := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun v _ => by rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [e2] at h
  exact (mul_le_mul (h1 m) (h k) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {T : Type} [Fintype T] [DecidableEq T] (I : Finset T) {n : ℕ}
    (lam : T → DomWeight n) (A : T → GL (Fin n) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (h : ∀ τ i j, (‖ι.symm (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) :
    ‖ι.symm (Formalism.L2.DIV.detTwK lam A)‖ ≤ R ^ (∑ τ, if τ ∈ I then n * (lam τ).detShift.natAbs else 0) := by
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have hR' : 1 ≤ if τ ∈ I then R else 1 := by split_ifs; exacts [hR, le_rfl]
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) _ hR' fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) _ hR' fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have e : R ^ (if τ ∈ I then n * (lam τ).detShift.natAbs else 0) =
      ((if τ ∈ I then R else 1) ^ n) ^ (lam τ).detShift.natAbs := by
    split_ifs <;> simp [pow_mul]
  rw [e]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k

theorem rho_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (W : Wt E a) [DecidableEq (InfinitePlace E)]
    (I : Finset (InfinitePlace E)) (A : InfinitePlace E → GL (Fin a) ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hA : ∀ τ i j, (‖ι.symm (((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ if τ ∈ I then R else 1) ∧
      ‖ι.symm ((((A τ)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)‖ ≤ if τ ∈ I then R else 1)
    (x : W.Sp) (hx : CoefLe ι 1 x.1) :
    CoefLe ι (R ^ (a * ∑ v ∈ I, 2 * sz (W v))) (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1 := by
  intro m
  have hb := block_le ι I (fun τ => Matrix.transpose ((A τ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)) R hR
    (fun τ i j => by simpa [Matrix.transpose_apply] using (hA τ j i).1) _ x.1 (homog_of_mem I a W x.1 x.2) hx m
  have hd := det_le ι I W A R hR hA
  have hcoe : (Formalism.L2.DIV.rhoK (K := ℂ) W A x).1 =
      Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A x.1 := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := by linarith
  refine (mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)).trans ?_
  rw [← pow_add]
  refine pow_le_pow_right₀ hR ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_ite_mem_eq I]
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs
  · rw [add_comm]; exact one_le (W v)
  · simp

end UpperTheory.Gal.Gen.Loc
end

