module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ContOfRightInv
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CompanionTheory.TwY PositivityTheory.RgBcC.Bridge

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting

private theorem cont_of_right_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) {f : G → ℂ} (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) : Continuous f := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq f).2 fun g => ?_)
  have ho : IsOpen {y : G | g⁻¹ * y ∈ K} := hK.preimage (continuous_const.mul continuous_id)
  filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ K by simp)] with y hy
  rw [← hf g _ hy, mul_inv_cancel_left]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def Fx (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) : Submodule ℂ π.V where
  carrier := {ψ | ∀ k ∈ K, finRep E n k ψ.1 = ψ.1}
  add_mem' {a b} ha hb k hk := by rw [Submodule.coe_add, map_add (f := _), ha k hk, hb k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c a ha k hk := by rw [Submodule.coe_smul, map_smul, ha k hk]

private def res (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (T : Module.End ℂ (Sm E n)) (h1 : T ∈ stabAlg π)
    (h2 : ∀ k, Commute T (finRep E n k)) : Module.End ℂ (Fx π K) :=
  (T.restrict (p := π.V) (q := π.V) h1).restrict fun ψ hψ k hk => by
    change finRep E n k (T ψ.1) = T ψ.1
    rw [← Module.End.mul_apply, ← (h2 k).eq, Module.End.mul_apply, hψ k hk]

private theorem eopW_comm (w : InfinitePlace E) (s : Bool) (a b : Fin n) (k : GL (Fin n) (Af E)) :
    Commute (eopW w s a b) (finRep E n k) := by
  have h : ∀ i j x, Commute (lieS E n i j x) (finRep E n k) := fun i j x => lie_rt_fin _ k
  have h' : ∀ τ : E →+* ℂ, Commute (Eop τ a b) (finRep E n k) := fun τ =>
    ((h a b _).sub_left ((h a b _).smul_left _)).smul_left _
  cases s
  · exact h' _
  · exact h' _

private theorem sV_mem (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (w : InfinitePlace E) (c : Un n) :
    ∀ ψ ∈ Fx π K, sV π w c ψ ∈ Fx π K := fun ψ hψ k hk => by
  change rt E n (finGL E n k) (rt E n (infGL E n (locInf w (Unitary.toUnits c))) ψ.1) =
    rt E n (infGL E n (locInf w (Unitary.toUnits c))) ψ.1
  rw [← Module.End.mul_apply, ← map_mul, ← infGL_comm, map_mul, Module.End.mul_apply]
  exact congrArg _ (hψ k hk)

private def sF (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (w : InfinitePlace E) :
    Un n →* Module.End ℂ (Fx π K) where
  toFun c := (sV π w c).restrict (sV_mem π K w c)
  map_one' := LinearMap.ext fun ψ => Subtype.ext (by simp)
  map_mul' a b := LinearMap.ext fun ψ => Subtype.ext (by simp)

private theorem along_unit (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (c : Un n) :
    along w g φ c.1 = φ (g * kAt w c) := by
  have e : atW w c.1 = toL (locInf w (Unitary.toUnits c)).val := by
    funext i j v
    exact (locInf_apply w (Unitary.toUnits c) i j v).symm
  rw [along, e, chart_val]
  rfl

private theorem fix_apply {π : CuspSub E n} {K : Subgroup (GL (Fin n) (Af E))} {ψ : π.V} (hψ : ψ ∈ Fx π K)
    {k : GL (Fin n) (Af E)} (hk : k ∈ K) (x : GA E n) : ψ.1.1 (x * finGL E n k) = ψ.1.1 x :=
  (rt_apply (finGL E n k) x ψ.1).symm.trans (congrArg (fun φ : Sm E n => φ.1 x) (hψ k hk))

private theorem thV_mem (π : CuspSub E n) (hθ : ThetaFix π) (K : Subgroup (GL (Fin n) (Af E)))
    (hK : ∀ k ∈ K, thetaF E n k ∈ K) : ∀ ψ ∈ Fx π K, ThInv.thV π hθ ψ ∈ Fx π K := fun ψ hψ k hk =>
  Subtype.ext <| funext fun x => by
    refine (rt_apply (finGL E n k) x _).trans ?_
    rw [ThInv.thV_apply, ThInv.thV_apply, map_mul, ThInv.thetaA_finGL, fix_apply hψ (hK k hk)]

private theorem hecke_ex (hM : HeckeMem) (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E)))
    (ho : IsOpen (K : Set (GL (Fin n) (Af E)))) (hc : IsCompact (K : Set (GL (Fin n) (Af E))))
    [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E)))
    [μf.IsHaarMeasure] (h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}) :
    ∃ R : Module.End ℂ (Fx π K), ∀ u, (R u).1.1.1 = heckeOp μf h.1 u.1.1.1 := by
  have ex : ∀ u : Fx π K, ∃ v : Fx π K, v.1.1.1 = heckeOp μf h.1 u.1.1.1 := fun u => by
    obtain ⟨_, _, ψ', -, h1, h2⟩ := hM E n π K ho hc μf h.1 h.2 u.1
    exact ⟨⟨ψ', h2⟩, h1⟩
  choose r hr using ex
  have hint : ∀ (u : Fx π K) (x : GA E n), Integrable (fun g => h.1 g * u.1.1.1 (x * finGL E n g)) μf := fun u x => by
    refine Continuous.integrable_of_hasCompactSupport (cont_of_right_inv ho fun g k hk => ?_) h.2.1.mul_right
    have e := h.2.2 1 K.one_mem k hk g
    rw [one_mul] at e
    rw [e, map_mul, ← mul_assoc, fix_apply u.2 hk]
  refine ⟨{ toFun := r, map_add' := fun a b => ?_, map_smul' := fun c a => ?_ }, hr⟩ <;>
    refine Subtype.ext <| Subtype.ext <| Subtype.ext <| funext fun x => ?_
  · change (r (a + b)).1.1.1 x = (r a).1.1.1 x + (r b).1.1.1 x
    rw [hr, hr, hr, heckeOp, heckeOp, heckeOp, ← integral_add (hint a x) (hint b x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_add _ _ _
  · change (r (c • a)).1.1.1 x = c * (r a).1.1.1 x
    rw [hr, hr, heckeOp, heckeOp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    exact mul_left_comm _ _ _

@[reducible] private def core (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hH : IsPet π H) : InnerProductSpace.Core ℂ (Fx π K) where
  inner x y := H x.1 y.1
  conj_inner_symm x y := hH.1 _ _
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx]
    · exact (hH.2.1 _ hx).le
  add_left x y z := by simp
  smul_left x y c := by simp
  definite x hx := by
    by_contra h0
    have := hH.2.1 x.1 fun e => h0 (Subtype.ext e)
    have hx' : H x.1 x.1 = 0 := hx
    simp [hx'] at this

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlEx :
    PetEx → HeckeMem → RlEx := by
  intro hP hM E _ _ _ n hn π hθ K ho hc hK _ _ μf _
  obtain ⟨H, hH⟩ := hP E n hn π hθ
  choose R hR using hecke_ex hM π K ho hc μf
  letI c : InnerProductSpace.Core ℂ (Fx π K) := core π K H hH
  exact ⟨{
    U := Fx π K
    nacg := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    ips := InnerProductSpace.ofCore c.toCore
    i := (Fx π K).subtype
    inj := Subtype.val_injective
    rng := fun ψ => ⟨fun ⟨u, hu⟩ => hu ▸ u.2, fun h => ⟨⟨ψ, h⟩, rfl⟩⟩
    H := H
    pet := hH
    inner_eq := fun _ _ => rfl
    E1 := fun w a b => res π K _ (eopW_mem_stabAlg π w true a b) (eopW_comm w true a b)
    E2 := fun w a b => -res π K _ (eopW_mem_stabAlg π w false b a) (eopW_comm w false b a)
    σ := sF π K
    Θ := (ThInv.thV π hθ).restrict (thV_mem π hθ K hK)
    R := R
    hE1 := fun _ _ _ _ => rfl
    hE2 := fun _ _ _ _ => rfl
    hσ := fun w k u g => (rt_apply (kAt w k) g u.1.1).trans (along_unit w g _ k).symm
    hΘ := fun u g => ThInv.thV_apply π hθ u.1 g
    hR := hR }⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlTheta
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB GlobalTheory.CompanionTheory.TwY GlobalTheory.CompanionTheory.TwY.ThInv
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem along_unitary (w : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (k : Un n) :
    Bridge.along w g φ k.1 = φ (g * kAt w k) := by
  classical
  have e : Bridge.atW (E := E) w k.1 = toL (locInf w (Unitary.toUnits k)).val := by
    funext i j v
    rw [Bridge.atW]
    exact (locInf_apply w (Unitary.toUnits k) i j v).symm
  rw [Bridge.along, e, chart_val]
  rfl

private theorem eop_theta (w : InfinitePlace E) (a b : Fin n) {φ φ' : Sm E n}
    (h : ∀ x, φ'.1 x = φ.1 (thetaA E n x)) (x : GA E n) :
    (Bridge.eopW w true a b φ).1 (thetaA E n x) = -(Bridge.eopW w false b a φ').1 x := by
  open Matrix in
  let adjH : Lie E n →L[ℝ] Lie E n :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => toL (Matrix.of X)ᴴ
        map_add' := fun X Y => by
          rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add]; rfl
        map_smul' := fun t X => by
          rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial]; rfl }

  have adjH_apply (X : Lie E n) (i j : Fin n) : adjH X i j = star (X j i) := rfl

  have map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
      (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
      GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
    ext i j
    change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
    rw [h, ← map_inv]
    rfl

  have thetaA_infGL (y : GL (Fin n) (Cinf E)) :
      thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
      (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

  have thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
      (by rw [pFin_finGL]; rfl)

  have thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
    classical
    have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
    rw [e, thetaA_infGL]
    congr 1
    refine Units.ext ?_
    ext i j v
    rw [thetaR_val, ← map_inv, ← map_inv]
    change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
    rw [locInf_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
      simp [Matrix.star_apply]
    · simp only [hv, if_false]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

  have toL_thetaR (y : GL (Fin n) (Cinf E)) :
      toL (thetaR (starRingEnd (Cinf E)) n y).val = adjH (GlobalTheory.ThetaPull.invL (toL y.val)) := by
    rw [thetaR_val]
    ext i j : 2
    change starRingEnd (Cinf E) ((y⁻¹ : GL (Fin n) (Cinf E)).val j i) = star ((y.val)⁻¹ j i)
    rw [Matrix.coe_units_inv]
    rfl

  have chart_theta (φ : GA E n → ℂ) (g : GA E n) {x : Lie E n} (hx : x ∈ invSet E n) :
      chart (fun g => φ (thetaA E n g)) g x = chart φ (thetaA E n g) (adjH (GlobalTheory.ThetaPull.invL x)) := by
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [← toL_thetaR, chart_val, chart_val, map_mul, thetaA_infGL]

  have lieD_theta (X : Lie E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g : GA E n) :
      lieD X (fun g => φ (thetaA E n g)) g = -lieD (adjH X) φ (thetaA E n g) := by
    have e : chart (fun g => φ (thetaA E n g)) g =ᶠ[nhds (oneL E n)]
        chart φ (thetaA E n g) ∘ adjH ∘ GlobalTheory.ThetaPull.invL :=
      Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_theta φ g hx
    have h1 : (adjH ∘ GlobalTheory.ThetaPull.invL) (oneL E n) = oneL E n :=
      (toL_thetaR 1).symm.trans (by rw [map_one]; rfl)
    have h2 := HasFDerivAt.comp (oneL E n) (f := adjH ∘ GlobalTheory.ThetaPull.invL)
      (by rw [h1]; exact (differentiableAt_chart hφ (thetaA E n g)).hasFDerivAt)
      (adjH.hasFDerivAt.comp (oneL E n) GlobalTheory.ThetaPull.invL_smooth.2)
    unfold lieD
    rw [e.fderiv_eq, h2.fderiv]
    simp


  have atEmb_conjugate (w : InfinitePlace E) (z : ℂ) :
      atEmb (ComplexEmbedding.conjugate w.embedding) z = atEmb w.embedding (conj z) := by
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
      (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)) (ComplexEmbedding.isReal_iff.2 h.symm)
    unfold atEmb
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne, if_pos rfl]


  have star_atEmb (w : InfinitePlace E) (z : ℂ) : star (atEmb w.embedding z) = atEmb w.embedding (conj z) := by
    funext v
    simp only [atEmb, InfinitePlace.mk_embedding, if_true, Pi.star_apply]
    by_cases hv : v = w
    · subst hv; simp
    · classical
      rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, star_zero]

  let sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : Lie E n := toL (Matrix.single a b (atEmb w.embedding z))

  have adjH_sg (w : InfinitePlace E) (a b : Fin n) (z : ℂ) : adjH (sg w a b z) = sg w b a (conj z) := by
    funext i j
    rw [adjH_apply]
    change star (Matrix.single a b (atEmb w.embedding z) j i) = Matrix.single b a (atEmb w.embedding (conj z)) i j
    rw [Matrix.single_apply, Matrix.single_apply]
    by_cases h : a = j ∧ b = i
    · rw [if_pos h, if_pos h.symm, star_atEmb]
    · rw [if_neg h, if_neg fun h' => h h'.symm, star_zero]

  have Eop_apply (τ : E →+* ℂ) (a b : Fin n) (φ : Sm E n) (g : GA E n) :
      (Eop τ a b φ).1 g = (1 / 2 : ℂ) * (lieD (toL (Matrix.single a b (atEmb τ 1))) φ.1 g -
        Complex.I * lieD (toL (Matrix.single a b (atEmb τ Complex.I))) φ.1 g) := rfl
  have e : φ'.1 = fun x => φ.1 (thetaA E n x) := funext h
  have e1 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w true a b f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w a b 1) f.1 y - Complex.I * lieD (sg w a b Complex.I) f.1 y) := fun f y => by
    simp only [Bridge.eopW, if_true]
    exact Eop_apply _ a b f y
  have e2 : ∀ (f : Sm E n) (y : GA E n), (Bridge.eopW w false b a f).1 y =
      (1 / 2 : ℂ) * (lieD (sg w b a 1) f.1 y - Complex.I * lieD (sg w b a (-Complex.I)) f.1 y) := fun f y => by
    simp only [Bridge.eopW, Bool.false_eq_true, if_false]
    rw [Eop_apply, atEmb_conjugate, atEmb_conjugate]
    simp [sg]
  rw [e1, e2, e]
  simp only [lieD_theta _ φ.2, adjH_sg, map_one, map_neg, Complex.conj_I, neg_neg]
  ring

end

theorem rlTheta : RlTheta := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D
  open Matrix in
  have map_thetaR {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (c : R →+* R) (c' : S →+* S)
      (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin n) R) :
      GeneralLinearGroup.map p (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map p g) := by
    ext i j
    change p (c ((g⁻¹ : GL (Fin n) R).val j i)) = c' (((GeneralLinearGroup.map p g)⁻¹ : GL (Fin n) S).val j i)
    rw [h, ← map_inv]
    rfl

  have thetaA_infGL (y : GL (Fin n) (Cinf E)) :
      thetaA E n (infGL E n y) = infGL E n (thetaR (starRingEnd (Cinf E)) n y) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_infGL, pInf_infGL])
      (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

  have thetaA_finGL (k : GL (Fin n) (Af E)) : thetaA E n (finGL E n k) = finGL E n (thetaF E n k) :=
    ga_ext (by rw [thetaA, map_thetaR _ _ _ GlobalTheory.ThetaPull.pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
      (by rw [pFin_finGL]; rfl)

  have thetaA_kAt (w : InfinitePlace E) (c : UU n) : thetaA E n (kAt w c) = kAt w c := by
    classical
    have e : kAt w c = infGL E n (locInf w (Unitary.toUnits c)) := rfl
    rw [e, thetaA_infGL]
    congr 1
    refine Units.ext ?_
    ext i j v
    rw [thetaR_val, ← map_inv, ← map_inv]
    change star ((locInf w (Unitary.toUnits c)⁻¹ : GL (Fin n) (Cinf E)).val j i v) = _
    rw [locInf_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      change star ((star c.1 : Matrix (Fin n) (Fin n) ℂ) j i) = c.1 i j
      simp [Matrix.star_apply]
    · simp only [hv, if_false]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  have hext : ∀ x y : D.U, (∀ g, (D.i x).1.1 g = (D.i y).1.1 g) → x = y := fun x y h =>
    D.inj (Subtype.ext (Subtype.ext (funext h)))
  refine ⟨LinearMap.ext fun u => hext _ _ fun g => ?_, fun x y => ?_, fun w =>
    ⟨fun k => LinearMap.ext fun u => hext _ _ fun g => ?_, fun a b => LinearMap.ext fun u => hext _ _ fun g => ?_⟩⟩
  · change (D.i (D.Θ (D.Θ u))).1.1 g = (D.i u).1.1 g
    rw [D.hΘ, D.hΘ, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · rw [D.inner_eq, D.inner_eq]
    exact D.pet.2.2.2.2 _ _ _ _ (D.hΘ x) (D.hΘ y)
  · change (D.i (D.Θ (D.σ w k u))).1.1 g = (D.i (D.σ w k (D.Θ u))).1.1 g
    rw [D.hΘ, D.hσ, D.hσ, along_unitary, along_unitary, D.hΘ, map_mul, thetaA_kAt]
  · change (D.i (D.Θ (D.E1 w a b u))).1.1 g = (D.i (D.E2 w a b (D.Θ u))).1.1 g
    rw [D.hΘ, D.hE1, D.hE2]
    exact eop_theta w a b (D.hΘ u) g

end UpperTheory.V.Z.GSp4Splitting
end
end

