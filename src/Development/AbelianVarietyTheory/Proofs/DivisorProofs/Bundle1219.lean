module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.ConormalFrame

theorem sub_isLocalizedModule {X : Scheme.{0}} {F : X.Modules} [F.IsQuasicoherent] (N : Sub F)
    {U : X.Opens} (hU : IsAffineOpen U)
    (h : ∀ (f : Γ(X, U)) (t : Γ(F, U)),
      GlobalTheory.Twist.resM F (X.basicOpen_le f) t ∈ N.sec _ → ∃ n : ℕ, f ^ n • t ∈ N.sec U)
    (f : Γ(X, U)) : IsLocalizedModule.Away f (GlobalTheory.QCoh.resBasicOpen N.toMod f) := by
  refine (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff _ f).2 ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨n, t, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ s)
    obtain ⟨m, hm⟩ := h f t (by
      change F.presheaf.map _ t ∈ _
      rw [← e]
      exact (N.sec _).smul_mem _ (N.incl_app_mem s))
    refine ⟨m + n, N.mkSec _ hm, N.incl_app_injective _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, GlobalTheory.QCoh.app_res, Sub.incl_app_mkSec, Scheme.Modules.map_smul,
      ← e, pow_add, mul_smul, map_pow]
  · obtain ⟨n, e⟩ := GlobalTheory.QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl
      (N.incl.app _ t) (by rw [← GlobalTheory.QCoh.app_res, ht, map_zero])
    exact ⟨n, N.incl_app_injective _ (by rw [Scheme.Modules.Hom.app_smul, e, map_zero])⟩

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}


include he in
theorem preimage_eq (c : IsChart π e U W) : e ⁻¹ᵁ W = U :=
  le_antisymm ((le_preimage_iff he).1 (e.preimage_mono c.le_base)) c.le


include he in
theorem isQuasicoherent_restrict_ideal (c : IsChart π e U W) :
    ((ideal e).restrict c.affine.fromSpec).IsQuasicoherent := by
  have := (isVB_structureModule X).isQuasicoherent
  refine (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine).2
    (sub_isLocalizedModule _ c.affine fun f (t : Γ(X, W)) ht => ?_)
  have hcpt : IsCompact ((e ⁻¹ᵁ W : S.Opens) : Set S) := by
    rw [preimage_eq he c]; exact c.affine_base.isCompact
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact S
    (U := e ⁻¹ᵁ W) hcpt (e.appLE W _ le_rfl t) (e.appLE W _ le_rfl f) (by
      have hle : S.basicOpen (e.appLE W _ le_rfl f) ≤ e ⁻¹ᵁ X.basicOpen f := by
        rw [Scheme.Hom.appLE_eq_app, e.preimage_basicOpen]
      have := congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG S hle)
        (show e.appLE _ _ le_rfl (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X (X.basicOpen_le f) t) = 0 from ht)
      rw [GlobalTheory.DualPull.resG_appLE, GlobalTheory.DualPull.appLE_resG, map_zero] at this
      exact (GlobalTheory.DualPull.resG_appLE e _ _ _).trans this)
  refine ⟨n, ?_⟩
  change e.appLE W _ le_rfl (f ^ n * t) = 0
  rw [map_mul, map_pow, hn]

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}


include he in
theorem isQuasicoherent_conormal : (conormal e).IsQuasicoherent := by
  refine GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  have := isQuasicoherent_restrict_ideal he c
  refine ⟨U, c.affine_base, hx,
    (GlobalTheory.QCoh.isQuasicoherent_restrict_fromSpec_iff _ c.affine_base).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(S, U)).ringCatSheaf).prop_of_iso
    ((GlobalTheory.QCoh.restrictPullbackIso
      (IsAffineOpen.SpecMap_appLE_fromSpec e c.affine c.affine_base c.le)).app (ideal e))
    (GlobalTheory.QCoh.isQuasicoherent_pullback_Spec (e.appLE W U c.le) ((ideal e).restrict c.affine.fromSpec))

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

open GlobalTheory.QCoh


set_option backward.isDefEq.respectTransparency false in
theorem isBaseChange_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    [(G.restrict hV.fromSpec).IsQuasicoherent] (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  obtain ⟨a, ha⟩ := exists_equiv_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec)
  have w := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let κ : Γ((Scheme.Modules.pullback (Spec.map (f.appLE V U e))).obj (G.restrict hV.fromSpec), ⊤)
      ≃ₗ[Γ(X, U)] Γ(((Scheme.Modules.pullback f).obj G).restrict hU.fromSpec, ⊤) :=
    (moduleSpecΓFunctor.mapIso ((restrictPullbackIso w).app G)).toLinearEquiv
  refine IsBaseChange.of_equiv
    ((sectionsEquivFromSpec G hV).baseChange Γ(Y, V) Γ(X, U) _ _ ≪≫ₗ a ≪≫ₗ κ ≪≫ₗ
      (sectionsEquivFromSpec _ hU).symm) fun s ↦ ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, ha, sectionsEquivFromSpec_apply,
    sectionsEquivFromSpec_apply, res_pullbackSections]
  refine Eq.trans ?_ (restrictPullbackIso_hom_app_pullbackSections w G (V' := ⊤) (U' := ⊤)
    (fromSpec_image_le hV ⊤) le_rfl _ s)
  exact congr(κ $(res_self _ le_rfl _)).symm

end GlobalTheory.ConormalFrame

namespace GlobalTheory.ConormalFrame

variable {S X : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (he : e ≫ π = 𝟙 S) {U : S.Opens}
  {W : X.Opens}

theorem ofAugCot_bijective (c : IsChart π e U W) : Function.Bijective (c.ofAugCot he) := by
  letI := c.algebra
  letI := GlobalTheory.QCoh.appLEAlgebra e c.le
  letI := GlobalTheory.QCoh.appLEModule e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := GlobalTheory.QCoh.appLE_isScalarTower e ((Scheme.Modules.pullback e).obj (ideal e)) c.le
  haveI := AugCot.isScalarTower_of_algebraMap_eq (c.aug he) fun _ => rfl
  haveI := isQuasicoherent_restrict_ideal he c
  have hb := isBaseChange_pullbackSections e (ideal e) c.affine_base c.affine c.le
  let g : Γ(ideal e, W) →ₗ[Γ(X, W)] AugCot (c.aug he) := (RingHom.ker (c.aug he)).toCotangent ∘ₗ
    (GlobalTheory.QCoh.appLinear (idealSub e).incl W).codRestrict (RingHom.ker (c.aug he)) fun s =>
      (c.aug_eq_zero_iff he).2 ((idealSub e).incl_app_mem s)
  have key (x : RingHom.ker (c.aug he)) : c.ofAugCot he ((RingHom.ker (c.aug he)).toCotangent x) =
      cls c.le x ((c.aug_eq_zero_iff he).1 x.2) := d_eq_cls he _ _ _
  refine Function.bijective_iff_has_inverse.2 ⟨hb.lift g, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := (RingHom.ker (c.aug he)).toCotangent_surjective x
    rw [key]
    exact hb.lift_eq g _
  · refine hb.inductionOn y (fun s => ?_) (fun r y hy => ?_) fun y z hy hz => ?_
    · rw [hb.lift_eq]
      exact key _
    · rw [map_smul, map_smul, hy]
      rfl
    · rw [map_add (f := _), map_add (f := _), hy, hz]
      rfl


include he in
theorem exists_isFrame [Smooth π] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(conormal e, U)), x ∈ U ∧ IsFrame s := by
  have := isQuasicoherent_conormal he
  obtain ⟨U, W, hx, -, c⟩ := exists_isChart he (x := x) (V := ⊤) trivial
  letI := c.algebra
  have : Algebra.Smooth Γ(S, U) Γ(X, W) := Smooth.smooth_appLE π c.affine_base c.affine c.le_base
  let E := LinearEquiv.ofBijective (c.ofAugCot he) (ofAugCot_bijective he c)
  have := Module.Finite.equiv E
  have := Module.Projective.of_equiv E
  exact Summand.exists_frame_of_projective c.affine_base ⟨x, hx⟩

end GlobalTheory.ConormalFrame

theorem GlobalTheory.ConormalFrame.exists_isFrame_omega : ∀ (O : Type) [CommRing O] (A : Over (Sp O))
    [GrpObj A] [Smooth A.hom] (x : Sp O), ∃ (U : (Sp O).Opens) (n : ℕ)
    (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s :=
  fun _ _ A _ _ x => GlobalTheory.ConormalFrame.exists_isFrame (GlobalTheory.LieVB.sec_hom η[A]) x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianDecompositionInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertWitt

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  LinearMap.range (LinearMap.pi fun i : Fin n => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i))

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (x : Fin n → E) :
    x ∈ stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).2
  · intro h
    refine ⟨fun i => ⟨x i, h i⟩, funext fun i => rfl⟩

theorem stdLat_isLattice (E : Type) [Field E] [NumberField E] (n : ℕ) : (stdLat E n).IsLattice E := by
  refine ⟨?_, ?_⟩
  · rw [stdLat, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory.InertWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianSkewHermitianCompletionTensor
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SkewLagr

open Matrix

theorem det_hyp {L : Type*} [CommRing L] (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) L) (1 : Matrix (Fin m) (Fin m) L) 1 0 =
      (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁]
  simp [det_neg]

theorem exists_isLagr_of_local (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {L : Type} [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L]
    (c : L →ₐ[v.adicCompletion F] L) (hc : ∀ x, c (c x) = x) {δ : L} (hδ : δ ≠ 0) (hcδ : c δ = -δ)
    (m : ℕ) (J : Matrix (Fin (m + m)) (Fin (m + m)) L) (hJ : ∀ i j, c (J j i) = -J i j)
    (hd : J.det ≠ 0) (hx : ∃ x, J.det = x * c x) :
    ∃ Cy : Matrix (Fin (m + m)) (Fin m) L, GlobalTheory.WeilM.IsLagr c J Cy := by
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨x, hx⟩ := hx
  let σ : L ≃ₐ[v.adicCompletion F] L := AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)
  have hσc : ∀ y, σ y = c y := fun _ => rfl
  have h2 : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap (v.adicCompletion F) L) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hσ : σ ≠ 1 := by
    intro h
    have h1 : c δ = δ := by rw [← hσc, h]; rfl
    apply hδ
    have : (2 : L) * δ = 0 := by linear_combination hcδ - h1
    exact (mul_eq_zero.1 this).resolve_left h2
  let e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv
  let Hyp : Matrix (Fin (m + m)) (Fin (m + m)) L :=
    (fromBlocks 0 1 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).submatrix e.symm e.symm
  let H : Matrix (Fin (m + m)) (Fin (m + m)) L := δ • J
  have hH : ∀ a b, σ (H a b) = H b a := by
    intro a b
    simp only [H, Matrix.smul_apply, smul_eq_mul, hσc, map_mul, hcδ, hJ]
    ring
  have hHyp : ∀ a b, σ (Hyp a b) = Hyp b a := by
    intro a b
    simp only [Hyp, submatrix_apply]
    rcases e.symm a with i | i <;> rcases e.symm b with j | j <;>
      by_cases hij : i = j <;> simp [fromBlocks, one_apply, hij, eq_comm]
  have hdH : H.det = δ ^ (m + m) * J.det := by simp [H, det_smul]
  have hdHyp : Hyp.det = (-1) ^ m := by simp [Hyp, det_submatrix_equiv_self, det_hyp]
  have hs : ((-1 : L) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  obtain ⟨P, hP, hPeq⟩ := (GlobalTheory.HermLocal.congr_iff_adicCompletion F v L σ hσ hH hHyp
    (by rw [hdH]; exact mul_ne_zero (pow_ne_zero _ hδ) hd) (by rw [hdHyp]; simp)).2 ⟨δ ^ m * x, by
      rw [hdH, hdHyp, div_eq_iff (by simp), hx, hσc, map_mul, map_pow, hcδ, neg_pow]
      linear_combination (-(δ ^ (m + m) * x * c x)) * hs⟩
  have hQ : ∀ a b, δ * (Pᵀ * J * P.map c) a b = Hyp a b := by
    intro a b
    rw [hPeq]
    simp only [H, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    rfl
  have hiso : ∀ (f : Fin m → Fin m ⊕ Fin m), (∀ a b, Hyp (e (f a)) (e (f b)) = 0) →
      (P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c = 0 := by
    intro f hf
    ext a b
    have h1 : ((P.submatrix id (fun j => e (f j)))ᵀ * J * (P.submatrix id (fun j => e (f j))).map c) a b =
        (Pᵀ * J * P.map c) (e (f a)) (e (f b)) := rfl
    rw [h1, Matrix.zero_apply]
    have h3 := hQ (e (f a)) (e (f b))
    rw [hf] at h3
    exact (mul_eq_zero.1 h3).resolve_left hδ
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hcols : fromCols (P.submatrix id (fun j => e (Sum.inl j))) (P.submatrix id (fun j => e (Sum.inr j))) =
      P.submatrix id e := by
    ext i (j | j) <;> rfl
  refine ⟨P.submatrix id (fun j => e (Sum.inl j)), hiso Sum.inl (fun a b => by simp [Hyp]),
    P.submatrix id (fun j => e (Sum.inr j)), P⁻¹.submatrix e id, hiso Sum.inr (fun a b => by simp [Hyp]), ?_, ?_⟩
  · rw [hcols, submatrix_mul_equiv, mul_nonsing_inv P hPu, submatrix_id_id]
  · rw [hcols, show (P⁻¹.submatrix e id) = P⁻¹.submatrix e (Equiv.refl _) from rfl,
      show P.submatrix id e = P.submatrix (Equiv.refl _) e from rfl, submatrix_mul_equiv,
      nonsing_inv_mul P hPu, submatrix_one_equiv]

end GlobalTheory.SkewLagr

namespace GlobalTheory.SkewLagr

open Matrix

theorem exists_isLagr_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)), IsField (Fv F v ⊗[F] E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Even n → (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 →
    (∃ x : Fv F v ⊗[F] E, (1 : Fv F v) ⊗ₜ[F] J.det = x * Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ x) →
    ∃ Cy : Matrix (Fin n) (Fin (n / 2)) (Fv F v ⊗[F] E),
      IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) J) Cy := by
  intro F E _ _ _ _ _ σ hcm v hF n J hn hJ hd hx
  obtain ⟨m, rfl⟩ := hn
  rw [show (m + m) / 2 = m by omega]
  letI : Field (Fv F v ⊗[F] E) := hF.toField
  haveI : Algebra.IsQuadraticExtension (Fv F v) (Fv F v ⊗[F] E) :=
    { finrank_eq_two' := by rw [Module.finrank_baseChange]; exact hcm.2.2.1 }
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ y, σ (σ y) = y := fun y => τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra h
    push_neg at h
    have hw := hcm.2.1.isComplex (NumberField.InfinitePlace.mk τ)
    rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hw
    apply hw
    ext y
    have hy := hcm.2.2.2 τ y
    rw [h] at hy
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [starRingEnd_apply]
    exact hy.symm
  set c := Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ with hcdef
  have hct : ∀ y : E, c ((1 : Fv F v) ⊗ₜ[F] y) = (1 : Fv F v) ⊗ₜ[F] σ y := fun y => by
    simp [c, Algebra.TensorProduct.map_tmul]
  have hc : ∀ z, c (c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [c, Algebra.TensorProduct.map_tmul, hσσ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hinj : Function.Injective (inclR (Fv F v) : E →+* Fv F v ⊗[F] E) := RingHom.injective _
  have hincl : ∀ y : E, inclR (Fv F v) y = (1 : Fv F v) ⊗ₜ[F] y := fun _ => rfl
  have hδ : (1 : Fv F v) ⊗ₜ[F] (t - σ t) ≠ 0 := by
    rw [← hincl]
    exact (map_ne_zero_iff _ hinj).2 (sub_ne_zero.2 (Ne.symm ht))
  have hcδ : c ((1 : Fv F v) ⊗ₜ[F] (t - σ t)) = -((1 : Fv F v) ⊗ₜ[F] (t - σ t)) := by
    rw [hct, map_sub, hσσ, ← TensorProduct.tmul_neg, neg_sub]
  have hdet : (JR (Fv F v) J).det = (1 : Fv F v) ⊗ₜ[F] J.det := by
    rw [← hincl, RingHom.map_det]
    rfl
  refine exists_isLagr_of_local F v c hc hδ hcδ m (JR (Fv F v) J) (fun i j => ?_) ?_ ?_
  · change c (inclR (Fv F v) (J j i)) = -inclR (Fv F v) (J i j)
    rw [hincl, hincl, hct, hJ, TensorProduct.tmul_neg]
  · rw [hdet, ← hincl]
    exact (map_ne_zero_iff _ hinj).2 hd
  · rw [hdet]
    exact hx

end GlobalTheory.SkewLagr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open Formalism.BasicNotions.TH

namespace GlobalTheory.FockQuot

variable (P Q R S : ℕ)

def rel (x : ℚ) : Submodule ℂ (Pol P Q R S) :=
  Submodule.span ℂ {g | ∃ (X : Mat P Q) (f : Pol P Q R S), g = fockAct1 P Q R S X f - ((x : ℂ) * X.trace) • f}

def act2 (t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S) :=
  fockAct2 P Q R S + (Matrix.traceLinearMap (Ix R S) ℂ ℂ).smulRight ((t : ℂ) • (1 : Module.End ℂ (Pol P Q R S)))

theorem fockSecondActionTraceShift_apply (t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    act2 P Q R S t Y f = fockAct2 P Q R S Y f + ((t : ℂ) * Y.trace) • f := by
  simp [act2, mul_comm, smul_smul]

theorem fockTraceCharacterRelations_le_comap_secondAction (x t : ℚ) (Y : Mat R S) : rel P Q R S x ≤ (rel P Q R S x).comap (act2 P Q R S t Y) := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨X, f, rfl⟩
  have hc : fockAct2 P Q R S Y (fockAct1 P Q R S X f) = fockAct1 P Q R S X (fockAct2 P Q R S Y f) :=
    (LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.2 X Y) f).symm
  refine Submodule.subset_span ⟨X, act2 P Q R S t Y f, ?_⟩
  simp only [fockSecondActionTraceShift_apply, map_sub, map_add (f := _), map_smul, hc]

theorem isLieAct_fockSecondActionTraceShift (t : ℚ) : IsLieAct (act2 P Q R S t) := by
  intro X Y
  refine LinearMap.ext fun f => ?_
  have h := LinearMap.congr_fun ((GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, fockSecondActionTraceShift_apply, map_add (f := _), map_smul, h, Matrix.trace_sub,
    Matrix.trace_mul_comm X Y, sub_self, mul_zero, zero_smul, add_zero]
  module

def actQ (x t : ℚ) : Mat R S →ₗ[ℂ] Module.End ℂ (Pol P Q R S ⧸ rel P Q R S x) where
  toFun Y := (rel P Q R S x).mapQ (rel P Q R S x) (act2 P Q R S t Y) (fockTraceCharacterRelations_le_comap_secondAction P Q R S x t Y)
  map_add' Y Z := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]
  map_smul' c Y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    simp [Submodule.mapQ_apply]

theorem actQ_mk (x t : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    actQ P Q R S x t Y (Submodule.Quotient.mk f) = Submodule.Quotient.mk (act2 P Q R S t Y f) := rfl

theorem actQ_lie (x t : ℚ) : IsLieAct (actQ P Q R S x t) := by
  intro X Y
  refine LinearMap.ext fun v => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have h := LinearMap.congr_fun (isLieAct_fockSecondActionTraceShift P Q R S t X Y) f
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
  simp only [actQ_mk, h, Submodule.Quotient.mk_sub]

theorem actQ_kfin (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    ∃ W : Submodule ℂ (Pol P Q R S ⧸ rel P Q R S x), FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (actQ P Q R S x t) W := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨W₀, hW₀, hf, hst⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  refine ⟨W₀.map (rel P Q R S x).mkQ, inferInstance, ⟨f, hf, rfl⟩, ?_⟩
  rintro X hX _ ⟨w, hw, rfl⟩
  refine ⟨act2 P Q R S t X w, ?_, rfl⟩
  rw [fockSecondActionTraceShift_apply]
  exact W₀.add_mem (hst X hX w hw) (W₀.smul_mem _ hw)

theorem actQ_wt (x t : ℚ) (μ : Ix R S → ℚ) (g : Pol P Q R S) (hg : g ∈ wtSub (fockAct2 P Q R S) μ) :
    (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈ wtSub (actQ P Q R S x t) (fun a => μ a + t) := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hg ⊢
  intro a
  rw [actQ_mk, fockSecondActionTraceShift_apply, hg a]
  simp [Eab, Matrix.trace_single_eq_same, add_smul]

theorem actQ_wts (x t : ℚ) (v : Pol P Q R S ⧸ rel P Q R S x) :
    v ∈ ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hf := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).2
  refine Submodule.iSup_induction (fun μ => wtSub (fockAct2 P Q R S) μ)
    (motive := fun g => (Submodule.Quotient.mk g : Pol P Q R S ⧸ rel P Q R S x) ∈
      ⨆ μ : Ix R S → ℚ, wtSub (actQ P Q R S x t) μ) hf ?_ ?_ ?_
  · intro μ g hg
    exact Submodule.mem_iSup_of_mem _ (actQ_wt P Q R S x t μ g hg)
  · simp
  · intro g h hg hh
    rw [Submodule.Quotient.mk_add]
    exact Submodule.add_mem _ hg hh

def gkQ (x t : ℚ) : GKMod R S where
  V := Pol P Q R S ⧸ rel P Q R S x
  act := actQ P Q R S x t
  lie := actQ_lie P Q R S x t
  kfin := actQ_kfin P Q R S x t
  wts := actQ_wts P Q R S x t

theorem mk_fockFirstAction_eq_trace_smul (x : ℚ) (X : Mat P Q) (f : Pol P Q R S) :
    (Submodule.Quotient.mk (fockAct1 P Q R S X f) : Pol P Q R S ⧸ rel P Q R S x) =
      ((x : ℂ) * X.trace) • Submodule.Quotient.mk f := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨X, f, rfl⟩

end GlobalTheory.FockQuot
end
end

