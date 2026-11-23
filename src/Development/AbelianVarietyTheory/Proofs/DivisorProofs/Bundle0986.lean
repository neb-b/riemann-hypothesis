module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValueStatement
section
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ), ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  first | exact @GlobalTheory.PolRangeInf.exists_at_inf_values | exact GlobalTheory.PolRangeInf.exists_at_inf_values | (intros; apply GlobalTheory.PolRangeInf.exists_at_inf_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjForms

theorem exists_conjChar {J K : Type} [Group J] [Field K] (σ₀ σ : K →+* ℂ) (χ : J →* ℂˣ)
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ χ' : J →* ℂˣ, ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ) := by
  choose y hy using hχ
  have h0 : ∀ k, σ (y k) ≠ 0 := fun k h => by
    have h1 := hy k
    rw [(map_eq_zero σ).1 h, map_zero] at h1
    exact (χ k).ne_zero h1.symm
  have hm : ∀ k k', y (k * k') = y k * y k' := fun k k' => σ₀.injective (by
    rw [map_mul, hy, hy, hy, map_mul, Units.val_mul])
  refine ⟨MonoidHom.mk' (fun k => Units.mk0 _ (h0 k)) fun k k' => Units.ext ?_, fun k => ⟨y k, hy k, rfl⟩⟩
  simp only [Units.val_mul, Units.val_mk0, hm, map_mul]

theorem exists_baseChange {G Γ W W' K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W'] [Field K] [NumberField K] [StarRing K]
    [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} (σ : K →+* ℂ) {ρ : Γ →* Module.End ℂ W}
    (ρ' : Γ →* Module.End ℂ W') {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (c₁ : M →ₛₗ[σ] W') (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, (∀ v, c₀ (T v) = ρ γ (c₀ v)) ∧ ∀ v, c₁ (T v) = ρ' γ (c₁ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) :
    ∃ (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H),
      (∃ χ' : J →* ℂˣ, (∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ) ∧ σ y = ((χ' k : ℂˣ) : ℂ)) ∧
        H.Is (Bridge.AdForms ι ρ' J χ') (Bridge.adInner ι J P.y)) ∧
      ∀ x h, ∃ v, P.extL x h = c₀ v ∧ H.e (j x) h = c₁ v := by
  obtain ⟨χ', hχ'⟩ := exists_conjChar σ₀ σ χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.AdFormsModel.exists_hmod_adForms G Γ W' ι ρ' J χ' S.Cl P.y P.reps
    fun c => Finite.of_equiv _ (P.stabI c).toEquiv
  have hinj : Function.Injective c₀ := by
    intro v v' h
    obtain ⟨x, rfl⟩ := e.surjective v
    obtain ⟨x', rfl⟩ := e.surjective v'
    rw [← he, ← he] at h
    rw [GlobalTheory.PresBasic.coef_injective P h]
  have hv : ∀ (x : S.Forms) h, ∃ v, P.extL x h = c₀ v := by
    intro x h
    obtain ⟨y, hy, -⟩ := hχ' (P.decK h)
    obtain ⟨T, hT, -⟩ := hact (P.decG h)
    refine ⟨y • T (e ((x : S.Cl → S.V) (P.decC h))), ?_⟩
    rw [map_smulₛₗ, hy, hT, ← he]
    rfl
  choose v hv using hv
  obtain ⟨j, hj⟩ := GlobalTheory.HilbertModel.exists_lift_fun σ hH (fun x h => c₁ (v x h))
    (fun a b => by
      funext h
      have : v (a + b) h = v a h + v b h := hinj (by rw [map_add (f := _), ← hv, ← hv, ← hv, map_add (f := _)]; rfl)
      rw [this, map_add (f := _)]; rfl)
    (fun c a => by
      funext h
      have : v (c • a) h = c • v a h := hinj (by rw [map_smulₛₗ, ← hv, ← hv, map_smulₛₗ]; rfl)
      rw [this, map_smulₛₗ]; rfl)
    (fun a γ h k => by
      obtain ⟨y, hy, hy'⟩ := hχ' k
      obtain ⟨T, hT, hT'⟩ := hact γ
      have : v a (ι γ * h * k) = y • T (v a h) := hinj (by
        rw [map_smulₛₗ, hy, hT, ← hv, ← hv]
        exact GlobalTheory.PresBasic.extMem P a γ h k)
      show c₁ (v a (ι γ * h * k)) = _
      rw [this, map_smulₛₗ, hy', hT'])
  exact ⟨H, j, ⟨χ', hχ', hH⟩, fun x h => ⟨v x h, hv x h, congrFun (hj x) h⟩⟩

theorem factor_mem {I : Type} [Fintype I] {k : I → Type} [∀ a, CommRing (k a)] {r : ℕ} (hr : 0 < r) (S : Subfield ℂ)
    (c : ∀ a, (k a)ˣ →* ℂˣ)
    (h : ∀ g : ∀ a, GL (Fin r) (k a), (∏ a, ((c a (Matrix.GeneralLinearGroup.det (g a)) : ℂˣ) : ℂ)) ∈ S)
    (a : I) (u : (k a)ˣ) : ((c a u : ℂˣ) : ℂ) ∈ S := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin r) (R := k a) u
  have h1 := h (Pi.mulSingle a g)
  rw [Finset.prod_eq_single a] at h1
  · rwa [Pi.mulSingle_eq_same, hg] at h1
  · intro b _ hb
    simp [Pi.mulSingle_eq_of_ne hb]
  · simp

theorem levFn_mem {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hg : ∀ PP ∈ L.Pg, ∀ c u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hq : L.Q = ∅) (x : GL (Fin n) (Lev.EAf D)) :
    ((levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  have h1 : ext1 (Lev.flag1L L).P.H (Lev.flag1L L).P.chi (rTup β (Lev.flag1L L) x) = 1 := Lev.subgroupCharExtension_one_apply _ _
  have h2 : (Lev.flag1L L).Q = ∅ := hq
  unfold levFn
  rw [h1, h2, one_mul, Finset.prod_empty, mul_one, Units.coe_prod]
  refine prod_mem fun PP hP => ?_
  rw [Units.coe_prod]
  exact prod_mem fun c _ => hg PP hP _ _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨γ, hγ⟩ := γ
  unfold GQ HFinIn at hγ
  obtain ⟨g, -, hg⟩ := hγ
  exact ⟨g, hg.symm⟩

theorem chi_mem (R : RealDat D A Ks) (hW : R.grp_chiW) (i : Fin D.R.m) (PP : Pl D.host.E) (hP : PP ∈ R.Pg) (u : (kP PP)ˣ) :
    ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  refine factor_mem (I := R.Pg) (k := fun PP => kP PP.1) hr _ (fun PP => R.chi ((i : ℕ) + 1) PP.1) (fun g => ?_) ⟨PP, hP⟩ u
  have h := hW i (R.eG.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  exact ⟨_, h⟩

theorem levChar_mem (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (i : Fin D.R.m) (k : levJ R i A.μ0) :
    ∃ y, D.what₂.embLL y = (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) := by
  have hQ : R.Q A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x _
    rfl
  refine levFn_mem (R.βV i) (R.datVt i A.μ0) D.what₂.embLL.fieldRange (fun PP hP c u => ?_) hQ _
  show (((R.chi ((i : ℕ) + 1) PP u)⁻¹ : ℂˣ) : ℂ) ∈ _
  rw [Units.val_inv_eq_inv_val]
  exact inv_mem (chi_mem R hW i PP hP u)


end GlobalTheory.ConjForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCoStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  first | exact @GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | exact GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | (intros; apply GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionExtendSwappingHyperbolicPa
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanPlane

open Matrix

theorem star_mulVec_map {m k : Type} [Fintype k] (B : Matrix m k ℂ) (v : k → ℂ) :
    star (B *ᵥ v) = B.map star *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, star_sum]

theorem form_mulVec {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix m l ℂ)
    (M : Matrix m m ℂ) (u : k → ℂ) (v : l → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (B *ᵥ v) = u ⬝ᵥ (Aᵀ * M * B.map star) *ᵥ star v := by
  rw [star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm]

theorem herm_swap {m : Type} [Fintype m] (M : Matrix m m ℂ) (hM : Mᴴ = M) (x y : m → ℂ) :
    y ⬝ᵥ M *ᵥ star x = star (x ⬝ᵥ M *ᵥ star y) := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by rw [← conjTranspose_apply, hM]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_form {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, x ⬝ᵥ A *ᵥ star y = x ⬝ᵥ B *ᵥ star y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

end GlobalTheory.CartanPlane

namespace GlobalTheory.CartanPlane
open Matrix

theorem extend_swap : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  intro n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁
  subst hn
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hYX : Yv ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap M hM, hXY]; simp
  have hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]
  have hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]
  have hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuX, star_zero]
  have hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuY, star_zero]
  have hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => form_mulVec ι ι M u u'
  have hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) =
      u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a' := by
    intro u a b u' a' b'
    simp only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul,
      dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]
    ring
  have hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a := by
    intro u a b; have := hexp u a b 0 0 1; simpa using this
  have hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b := by
    intro u a b; have := hexp u a b 0 1 0; simpa using this

  have hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv := by
    let Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ) :=
      (Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)
    have hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv := fun p => by simp [Φ]
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨u, w⟩ h0
      rw [hΦ] at h0
      have ha := hcY u (w 0) (w 1)
      have hb := hcX u (w 0) (w 1)
      simp only at h0 ha hb
      rw [h0, zero_dotProduct] at ha hb
      have hu : ι *ᵥ u = 0 := by rw [← ha, ← hb] at h0; simpa using h0
      have : u = 0 := by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]
      refine Prod.ext this ?_
      ext i; fin_cases i <;> simp [← ha, ← hb]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩

  set vX := M *ᵥ star X with hvX
  set vY := M *ᵥ star Yv with hvY
  set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁
  set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef
  have hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv := by
    intro u a b
    have ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a := by rw [dotProduct_comm]; exact hcY u a b
    have hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b := by rw [dotProduct_comm]; exact hcX u a b
    have hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u := by
      rw [hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]
      simp only [op_smul_eq_smul]
      abel
    rw [hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]
    simp only [op_smul_eq_smul]
    abel
  have hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ,
      (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B := by
    intro A B h
    apply ext_of_mulVec_single
    intro i
    obtain ⟨u, a, b, hz⟩ := hdec (Pi.single i 1)
    rw [hz, h]
  have hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u := fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]
  have hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => by
    rw [form_mulVec, hθ₁.2.1]
  have hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c := fun c => by
    simp [Complex.mul_re, Complex.normSq_apply]
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply hext
    intro u a b
    rw [← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]
  · apply ext_form
    intro x y
    rw [← form_mulVec]
    obtain ⟨u, a, b, rfl⟩ := hdec x
    obtain ⟨u', a', b', rfl⟩ := hdec y
    rw [hθ, hθ, hexp, hexp, hiso₁]
    ring
  · intro x hx
    obtain ⟨u, a, b, rfl⟩ := hdec x
    rw [hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]
    by_cases hu : u = 0
    · subst hu
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        simp [h.1, h.2]
      simp only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]
      rcases hab with h | h
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg b; linarith
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg a; linarith
    · have := hθ₁.2.2 u hu
      have := Complex.normSq_nonneg b; have := Complex.normSq_nonneg a; linarith
  · apply ext_of_mulVec_single
    intro j
    have := hθ (Pi.single j 1) 0 0
    simp only [zero_smul, add_zero] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, this]
  · have := hθ 0 1 0
    simpa using this

end GlobalTheory.CartanPlane
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanEx

open scoped ComplexOrder

private lemma map_star_mul' {l m k : Type} [Fintype m] (X : Matrix l m ℂ) (Y : Matrix m k ℂ) :
    (X * Y).map star = X.map star * Y.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private lemma map_star_star {l m : Type} (X : Matrix l m ℂ) : (X.map star).map star = X := by
  ext i j; simp

private lemma map_star_one {m : Type} [DecidableEq m] : (1 : Matrix m m ℂ).map star = 1 := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma star_mulVec_map {l m : Type} [Fintype m] (X : Matrix l m ℂ) (v : m → ℂ) :
    star (X *ᵥ v) = X.map star *ᵥ star v := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum]

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  intro n M r s ⟨hn, A, hA⟩
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by simp [hD, Matrix.fromBlocks_multiply]
  have hDT : Dᵀ = D := by simp [hD, Matrix.fromBlocks_transpose]
  have hDs : D.map star = D := by
    simp only [hD, Matrix.fromBlocks_map]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
  clear_value D
  set L := D * Aᵀ * M with hLdef
  clear_value L
  have hL : L * A.map star = 1 := by
    rw [hLdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, hDD]
  have e : Fin n ≃ Fin r ⊕ Fin s := (finSumFinEquiv.trans (finCongr hn)).symm
  have hR : A.map star * L = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hL
  have hR' : A * L.map star = 1 := by
    have := congrArg (fun X => Matrix.map X star) hR
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  have hL' : L.map star * A = 1 := by
    have := congrArg (fun X => Matrix.map X star) hL
    simpa only [map_star_mul', map_star_star, map_star_one] using this
  refine ⟨A * D * L.map star, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (L.map star) A, hL', Matrix.one_mul, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul, hR']
  · have hDL : D * L = Aᵀ * M := by
      rw [hLdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    calc (A * D * L.map star)ᵀ * M * (A * D * L.map star).map star
        = (L.map star)ᵀ * D * (Aᵀ * M * A.map star) * (D * L) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, map_star_mul', map_star_mul', map_star_star, hDs, hDT]
          simp only [Matrix.mul_assoc]
      _ = (A * L.map star)ᵀ * M := by
          rw [hA, hDL, Matrix.mul_assoc (L.map star)ᵀ D D, hDD, Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M := by rw [hR', Matrix.transpose_one, Matrix.one_mul]
  · intro x hx
    set a := L.map star *ᵥ x with ha_def
    have hxa : x = A *ᵥ a := by rw [ha_def, Matrix.mulVec_mulVec, hR', Matrix.one_mulVec]
    have ha : a ≠ 0 := by
      intro h; apply hx; rw [hxa, h, Matrix.mulVec_zero]
    have hθx : (A * D * L.map star) *ᵥ x = A *ᵥ (D *ᵥ a) := by
      rw [ha_def, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have key : ∀ b c : Fin r ⊕ Fin s → ℂ, (A *ᵥ b) ⬝ᵥ M *ᵥ (A.map star *ᵥ c) = b ⬝ᵥ (Aᵀ * M * A.map star) *ᵥ c := by
      intro b c
      rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
        ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
    have hval : ((A * D * L.map star) *ᵥ x) ⬝ᵥ M *ᵥ star x = a ⬝ᵥ star a := by
      rw [hθx]
      conv_lhs => rw [hxa, star_mulVec_map]
      rw [key, hA, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hDT, hDD, Matrix.vecMul_one]
    rw [hval]
    exact (Complex.pos_iff.mp (Matrix.dotProduct_self_star_pos_iff.mpr ha)).1

end GlobalTheory.CartanEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDimStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim : ∀ (K : Type) [Field K] (N D : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) → ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  first | exact @GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | exact GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | (intros; apply GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientMapExtensionRationalValues
section
noncomputable section

namespace GlobalTheory.Div.CoefExtension

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem exists_ext_placeEx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_chiW → R.IsFam → R.IsModels → ∀ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' (c0L i) c0' ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hW hF hM gramR c0R c0L hT i K' _ jL σ' hσ
  obtain ⟨c0', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (lamV D i) (c0L i)
  exact ⟨c0', hc, fun t Cl _ h =>
    GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hM.jV hT hc hL hW hF.pl_onto hF.muVal⟩

end GlobalTheory.Div.CoefExtension
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.UnitaryBC

namespace GlobalTheory.PolChar

theorem exists_compNorm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {χ : Formalism.L2.Host.HChar E} {u : ℝ},
    χ.IsAbsPow u → ∃ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E),
      GlobalTheory.GalOfCusp.compNorm E ψ = χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹ ∧
        ∀ v : InfinitePlace (maximalRealSubfield E), ψ.locInf v (-1) = 1 := by
  intro E _ _ _ χ u h
  refine ⟨resReal χ, Subtype.ext (MonoidHom.ext fun x => ?_), resReal_locInf_neg_one h⟩
  change χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
    χ.1 x * ((χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹)⁻¹
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, ideleConj_eq, inv_inv]

end GlobalTheory.PolChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLocalGaussSumNormSqEqAbsNormPowStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ), a ≠ 0 → ExpAt χ w a → IsUnitary χ → w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) → ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  exact @GlobalTheory.GaussMod.gaussSumAt_normSq
end

