module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemBasicOpenOfMemBasicOpenNormCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActRep
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

theorem actRep : ∀ D : D7, ActRep D := by
  intro D V β L S θ M hl hP
  have e : Formalism.IndefR.Lev.flag1L L = L := by
    rw [flag1L, withP, ← hP]
  have hM : Mult θ M (levS V β L) (levChi V β L) = MultP θ M β L := by
    rw [MultP, e]
  rw [hM]
  refine ⟨fun g T hT => act_mem g hT, fun T hT => act_one hT, fun g h T hT => act_mul hl g h hT, ?_⟩
  intro G _ _ eG c hc g T hT
  have h := gaL_act eG hl (c := c) (fun a b => hc a b) (eG.symm g) hT
  rwa [MulEquiv.apply_symm_apply] at h

end GlobalTheory.MultAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllPositiveModelFiniteDimensionalCompactType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactModel

theorem mem_Kset_of_mem_UJset {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g ∈ Formalism.REAL.Kset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rw [hJ, Matrix.mul_one] at h
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h, ?_⟩
  rw [hJ, Matrix.mul_one, Matrix.one_mul]

theorem list_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : (l.map fun x => g⁻¹ * x * g).prod = g⁻¹ * l.prod * g := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp [Matrix.nonsing_inv_mul _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem smoothVec_stable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ UJset ε) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ u w) := by
  obtain ⟨⟨h1, hmul⟩, -, -⟩ := hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : IsUnit (Formalism.REAL.Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul hJ).mul hP
  have hu' : uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε := hu
  have huu : IsUnit u := by
    have : IsUnit (uᴴ * Formalism.REAL.Jm ε * u) := by rw [hu']; exact hJ
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det u).2 (isUnit_of_mul_isUnit_right this)
  set g : Matrix (Fin n) (Fin n) ℂ := P⁻¹ * u * P with hgdef
  have hPi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hP
  have hg : IsUnit g := (hPi.mul huu).mul hP
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hPg : P * g = u * P := by
    rw [hgdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hug : u = P * g * P⁻¹ := by
    rw [hPg, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (uᴴ * Formalism.REAL.Jm ε * u) * P := by
          rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hu', h]
  clear_value g
  intro k Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := by
    intro i
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    have e1 : G * g⁻¹ = gᴴ * G := by
      conv_lhs => rw [← hgG]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    have e2 : (g⁻¹)ᴴ * G = G * g := by
      conv_lhs => rw [← hgG]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hgd]
      simp
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hw k (fun i => g⁻¹ * Xs i * g) hY
  have hs2 := ((σ u).restrictScalars ℝ).contDiff.comp hs
  convert hs2 using 1
  funext t
  have hmem : ∀ Zs : Fin k → Matrix (Fin n) (Fin n) ℂ, (∀ i, (Zs i)ᴴ * G + G * Zs i = 0) →
      P * (List.ofFn fun i => NormedSpace.exp (t i • Zs i)).prod * P⁻¹ ∈ UJset ε := fun Zs hZ => by
    refine GlobalTheory.GardingVec.conj_mem hP h (GlobalTheory.GardingVec.list_prod_mem _ fun a ha => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact GlobalTheory.GardingVec.exp_mem hG (hZ i) _
  have e3 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = g⁻¹ * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← list_prod_conj hg, List.map_ofFn]
    congr 2
    funext i
    rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hg]
    simp
  have a := hmul _ (hmem Xs hX) _ hu
  have b := hmul _ hu _ (hmem _ hY)
  have e4 : P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ * u
      = u * (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) := by
    rw [e3, hug]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.mul_nonsing_inv_cancel_left _ _ hgd]
  rw [e4, b] at a
  exact (congrArg (fun f => f w) a).symm

theorem model_allPos : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau),
    M.ε τ = allPos V.rank → FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧
      IsURepOn (UJset (allPos V.rank)) (M.σ τ) ∧
      IsKTypeOf (allPos V.rank) (M.σ τ) (Formalism.QuantumDeterminants.lowK (allPos V.rank) (M.lam τ)) ⊤ := by
  intro D V S M τ hε
  obtain ⟨-, -, hrep, hirr, -, ⟨T, hT⟩, -⟩ := M.ds τ
  have hT' := hT
  rw [hε] at hT'
  have hTtop : T = ⊤ := by
    obtain ⟨hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩ := hT'
    refine (hirr T T.closed_of_finiteDimensional fun g hg => hst g ?_).resolve_left ?_
    · rw [hε] at hg
      exact mem_Kset_of_mem_UJset hg
    · exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  subst hTtop
  have hfd : FiniteDimensional ℂ (M.H τ) := by
    have := hT'.1
    exact Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfd, ?_, hε ▸ hrep, hT'⟩
  refine (hirr (M.sm τ) (M.sm τ).closed_of_finiteDimensional fun u hu v hv => ?_).resolve_left
    (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  have hle : (M.sm τ).map (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ) ≤ M.sm τ := by
    refine (Submodule.map_span_le _ _ _).2 fun w hw => Submodule.subset_span ?_
    exact smoothVec_stable hrep (M.fr_unit τ) (M.fr_gram τ) hu hw
  exact hle ⟨v, hv, rfl⟩

end GlobalTheory.CompactModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormalDescent

theorem exists_sec_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X} (hM : M.IsLB) (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec,
      (∀ x : X, (∀ y : Y, f y = x → y ∈ nonzeroLocus t) → ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k)) ∧
      ∀ (x : X) (k : ℕ), 1 ≤ k → x ∈ nonzeroLocus (u k) → ∃ y ∈ nonzeroLocus t, f y = x := by
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.NormalDescent.exists_sec_normCoeff_local f hM t
  refine ⟨u, fun x hx => ?_, fun x k hk hx => ?_⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨k, hk, h⟩ := GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre f hV τ x hxV fun y hy => (ht y (hy ▸ hxV)).1 (hx y hy)
    exact ⟨k, hk, (hc k x hxV).2 h⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.NormalDescent.exists_mem_basicOpen_of_mem_basicOpen_normCoeff f hV τ x k hxV hk ((hc k x hxV).1 hx)
    exact ⟨y, (ht y hxV).2 hy, rfl⟩

theorem isAmpleLB_of_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X), AlgebraicGeometry.IsNoetherian X →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsFinite f → Function.Surjective f →
    ∀ L : ReciprocityTheory.ChartRestriction.G.Semi.LB X, L.IsLB → GlobalTheory.IsAmpleLB (L.pull f) → GlobalTheory.IsAmpleLB L := by
  intro X X' f _ hN _ hs L hL h
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have : Surjective f := ⟨hs⟩
  refine GlobalTheory.isAmpleLB_of_forall_le hL fun x U hx => ?_
  have hfin : (f ⁻¹' {x}).Finite := f.finite_preimage_singleton x
  obtain ⟨n, hn, s, hS, hle, -⟩ := h.exists_affine_finite_subset hfin (U := f ⁻¹ᵁ U)
    (fun y (hy : f y = x) => show f y ∈ U from hy ▸ hx)
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu₁, hu₂⟩ := exists_sec_image f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hxk⟩ := hu₁ x fun y hy => ht.ge (hS hy)
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hxk, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hu₂ z k hk (e.le hz)
  exact hle (ht.le hw)

end GlobalTheory.NormalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAdelicVectorDecomposition
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselDecomp

open GlobalTheory.BesselCompare (hA_add hA_smul hA_sum hA_vec hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem hD_basis_dual (d : BesselDatum A B ι) (i l) : B.hD (d.aux l) (dual d i) = if l = i then 1 else 0 := by
  have hz : star (B.hT d.z d.z) = B.hT d.z d.z := (hT_swap rfl).symm
  have zz : B.hT d.z d.z ≠ 0 := d.zz
  unfold BesselDatum.aux dual
  refine Fin.lastCases ?_ (fun j => ?_) i <;> refine Fin.lastCases ?_ (fun k => ?_) l
  · simp [HSpace.hD, starRingEnd_apply, hz, zz]
  · have : B.hT d.z (d.e k) = 0 := d.ez k
    simp [HSpace.hD, this, Fin.castSucc_ne_last]
  · rw [Fin.snoc_last, Fin.snoc_castSucc, hD_swap_zero (d.fz j), if_neg (Fin.castSucc_ne_last j).symm]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, d.ef]
    simp

theorem f_dual (d : BesselDatum A B ι) (i l) : B.hD (d.f l) (dual d i) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have : B.hT d.z (d.f l) = 0 := d.fz l
    simp [HSpace.hD, this]
  · rw [Fin.snoc_castSucc, d.ff]

theorem hD_basis_e (d : BesselDatum A B ι) (i l) : B.hD (d.aux i) (d.e l) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, hD_swap_zero (d.ez l)]
  · rw [Fin.snoc_castSucc, d.ee]

theorem f_e (d : BesselDatum A B ι) (k l) : B.hD (d.f k) (d.e l) = if k = l then 1 else 0 := by
  have h : B.hT (d.e l) (d.f k) = star (if l = k then 1 else 0) := hT_swap (d.ef l k)
  unfold HSpace.hD
  rw [h]
  by_cases e : k = l
  · simp [e]
  · simp [e, Ne.symm e]

def comb (d : BesselDatum A B ι) :
    (A.V × (Fin (d.ρ + 1) → D.host.E) × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
  ι.coprod ((Fintype.linearCombination D.host.E d.aux).coprod (Fintype.linearCombination D.host.E d.f))

theorem comb_inj (d : BesselDatum A B ι) : Function.Injective (comb d) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s, r⟩ h
  simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
  have h1 : ∀ i l, B.hT (dual d i) (d.aux l) = if l = i then 1 else 0 := hD_basis_dual d
  have h2 : ∀ i l, B.hT (dual d i) (d.f l) = 0 := f_dual d
  have h3 : ∀ i l, B.hT (d.e l) (d.aux i) = 0 := hD_basis_e d
  have h4 : ∀ k l, B.hT (d.e l) (d.f k) = if k = l then 1 else 0 := f_e d
  have h5 : ∀ i, B.hT (dual d i) (ι a) = 0 := fun i => hD_swap_zero (dual_perp d i a)
  have h6 : ∀ l, B.hT (d.e l) (ι a) = 0 := fun l => hD_swap_zero (d.eA l a)
  have hs : s = 0 := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, h1, h2, h5] using congrArg (B.hT (dual d i)) h
  have hr : r = 0 := by
    funext l
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, h3, h4, h6] using congrArg (B.hT (d.e l)) h
  subst hs hr
  have ha : ι a = 0 := by simpa using h
  have : a = 0 := by
    refine A.nondeg.1 a fun y => ?_
    rw [← d.isom a y, ha]; simp
  subst this
  rfl

theorem comb_surj (d : BesselDatum A B ι) : Function.Surjective (comb d) := by
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 (comb_inj d)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, A.rank_eq, B.rank_eq,
    d.rank_eq]
  omega

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {n : ℕ} (c : Fin n → D.host.E) (v : Fin n → B.V) :
    vecA B (∑ i, c i • v i) = ∑ i, incA D (c i) • vecA B (v i) := by
  funext k; simp [vecA, map_sum, Finset.sum_apply]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← A.frame.sum_repr a, map_sum]
  simp only [map_smul]
  rw [vecA_sum]
  rfl

theorem exists_comb (d : BesselDatum A B ι) (x : Fin B.rank → AE D) :
    ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      x = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l) := by
  have hx : x = ∑ k, x k • vecA B (B.frame k) := by
    funext j
    simp [vecA, Finset.sum_apply, Finsupp.single_apply, apply_ite (incA D)]
  rw [hx]
  refine Finset.sum_induction _ (fun y => ∃ (t : Fin A.rank → AE D) (s : Fin (d.ρ + 1) → AE D) (r : Fin d.ρ → AE D),
      y = iA ι t + ∑ i, s i • vecA B (d.aux i) + ∑ l, r l • vecA B (d.f l)) ?_ ?_ ?_
  · rintro _ _ ⟨t, s, r, rfl⟩ ⟨t', s', r', rfl⟩
    refine ⟨t + t', s + s', r + r', ?_⟩
    simp only [iA_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  · exact ⟨0, 0, 0, by simp [iA]⟩
  · intro k _
    obtain ⟨⟨a, s, r⟩, h⟩ := comb_surj d (B.frame k)
    simp only [comb, LinearMap.coprod_apply, Fintype.linearCombination_apply] at h
    refine ⟨x k • vecA A a, fun i => x k * incA D (s i), fun l => x k * incA D (r l), ?_⟩
    rw [← h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota, iA_smul]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_assoc]

theorem iA_vec {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (iA ι t) (vecA B v) = 0 := by
  rw [← hA_herm, hA_vec_iA h, map_zero]

theorem decomp : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (∀ i l, B.hD (d.aux l) (dual d i) = if l = i then 1 else 0) ∧ (∀ i l, B.hD (d.f l) (dual d i) = 0) ∧
    ∀ x : Fin B.rank → AE D, ∃ t, x = iA ι t + ∑ i, hA B x (vecA B (dual d i)) • vecA B (d.aux i) +
      ∑ l, hA B x (vecA B (d.e l)) • vecA B (d.f l) := by
  intro D A B ι d
  refine ⟨hD_basis_dual d, f_dual d, fun x => ?_⟩
  obtain ⟨t, s, r, h⟩ := exists_comb d x
  have hs : ∀ i, hA B x (vecA B (dual d i)) = s i := fun i => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (dual_perp d i)]
    simp [hA_smul, hA_vec, hD_basis_dual, f_dual, apply_ite (incA D)]
  have hr : ∀ l, hA B x (vecA B (d.e l)) = r l := fun l => by
    rw [h, hA_add, hA_add, hA_sum, hA_sum, iA_vec (d.eA l)]
    simp [hA_smul, hA_vec, hD_basis_e, f_e, apply_ite (incA D)]
  exact ⟨t, by simp only [hs, hr]; exact h⟩

end GlobalTheory.BesselDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepVectorsAndAdjointVectorsAreTheta
section
open Formalism.BasicNotions

namespace GlobalTheory.VecTheta

theorem vecThetaSD : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_stepVec h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_thPVec h⟩

end GlobalTheory.VecTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffIntegrableContinuousOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.CoefInt

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem continuous_psiN (d : BesselDatum A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) :
    Continuous (d.psiN ψ) := by
  have i0 : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hm : Continuous (mt B) := Units.continuous_val.comp continuous_subtype_val
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have ha : ∀ v, Continuous fun g => actV B g v := fun v => hm.matrix_mulVec continuous_const
  refine hψ.comp (ht.comp (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)))
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_const.mul ((continuous_apply b).comp (ha _))

def FlagCocompact : Prop :=
  ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k

theorem exists_compact (H : FlagCocompact) (d : BesselDatum A B ι) :
    ∃ K : Set (GA D B), IsCompact K ∧ ∀ n ∈ d.N, ∃ γ ∈ GQ B, ∃ k ∈ K, n = γ * k := by
  obtain ⟨K, hK, h⟩ := H D B _ (GlobalTheory.BesselCompare.toBes d).e (GlobalTheory.BesselCompare.toBes d).e_iso
  have hN := (GlobalTheory.BesselCompare.same_toBes d).2.2.1
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun n hn => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨n, hN ▸ hn⟩
  exact ⟨γ, hγ, k, ⟨k, hk, rfl⟩, congrArg Subtype.val e⟩

theorem coeff_integrable_continuous_of (H : FlagCocompact) : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 → ∀ F : GA D B → ℂ, Continuous F → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → (∀ g, IntegrableOn (fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))) 𝓝 ν) ∧ Continuous (d.coeff ψ ν 𝓝 F) ∧ ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M := by
  intro D A B ι d ψ hψ ν 𝓝 hν F hF hinv
  obtain ⟨b1, b2, b3, b4, b5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hbd : ∀ C : Set (GA D B), IsCompact C → ∃ M : ℝ, ∀ n ∈ d.N, ∀ g ∈ C, ‖F (n * g)‖ ≤ M := by
    intro C hC
    obtain ⟨K, hK, h⟩ := exists_compact H d
    obtain ⟨M, hM⟩ := (hK.mul hC).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨M, fun n hn g hg => ?_⟩
    obtain ⟨γ, hγ, k, hk, rfl⟩ := h n hn
    rw [mul_assoc, hinv γ hγ]
    exact hM _ (Set.mul_mem_mul hk hg)
  have hfin : ν 𝓝 ≠ ⊤ := by rw [hν.2.2]; exact ENNReal.one_ne_top
  have : SecondCountableTopology d.N := TopologicalSpace.Subtype.secondCountableTopology _
  have hχ : Continuous fun n : d.N => star (d.psiN ψ (n : GA D B)) :=
    ((continuous_psiN d hψ.1).comp continuous_subtype_val).star
  have hc : ∀ g, Continuous fun n : d.N => F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B)) := fun g =>
    (hF.comp (continuous_subtype_val.mul continuous_const)).mul hχ
  have hn : ∀ g (n : d.N), ‖F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B))‖ = ‖F ((n : GA D B) * g)‖ :=
    fun g n => by rw [norm_mul, norm_star, BesselDatum.psiN, hψ.2.1, mul_one]
  refine ⟨fun g => ?_, ?_, hbd⟩
  · obtain ⟨M, hM⟩ := hbd {g} isCompact_singleton
    exact Measure.integrableOn_of_bounded (M := M) hfin (hc g).measurable.aestronglyMeasurable
      (.of_forall fun n => (hn g n).trans_le (hM n n.2 g rfl))
  · refine continuous_iff_continuousAt.2 fun g => ?_
    obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
    obtain ⟨M, hM⟩ := hbd C hC
    have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hfin
    refine continuousAt_of_dominated (bound := fun _ => M)
      (.of_forall fun x => (hc x).measurable.aestronglyMeasurable) ?_ (integrable_const M)
      (.of_forall fun n => ?_)
    · filter_upwards [hCg] with x hx
      exact .of_forall fun n => (hn x n).trans_le (hM n n.2 x hx)
    · exact ((hF.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt

end GlobalTheory.RootExch.CoefInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfLevel
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.LevelForms

theorem finiteDimensional_of_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (GQ L n) W) (N : ℕ), 0 < N →
    ∀ S : Submodule ℂ (GAf L n → W), (∀ f ∈ S, f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
    FiniteDimensional ℂ S := by
  intro L _ _ _ n W _ _ _ ρ N hN S hS
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n ρ (_root_.GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n) hN
  refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n ρ N) fun f hf => ?_
  exact ⟨(hS f hf).1.1, fun κ hκ g => congrFun ((hS f hf).2 κ hκ) g⟩

end GlobalTheory.LevelForms
end

