module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrame
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.CoreIsom

theorem cT_add' {A : Type} [CommRing A] (s : A →+* A) {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A) :
    cT s (X + Y) = cT s X + cT s Y := by
  ext i k; simp [cT]

theorem unitary_core {A : Type} [CommRing A] (s : A →+* A) {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
    {J₀ : Matrix (Fin m) (Fin m) A} {C : Matrix (Fin n) (Fin j) A} {Z : Matrix (Fin n) (Fin m) A}
    {G : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin j) (Fin m) A}
    (hG : cT s G * J * G = J) (hcz : cT s C * J * Z = 0) (hzc : cT s Z * J * C = 0)
    (hcc : cT s C * J * C = 0) (hzz : cT s Z * J * Z = J₀) (hGZ : G * Z = Z * M + C * b) :
    cT s M * J₀ * M = J₀ := by
  have e : cT s (G * Z) * J * (G * Z) = J₀ := by
    calc cT s (G * Z) * J * (G * Z) = cT s Z * (cT s G * J * G) * Z := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J₀ := by rw [hG, hzz]
  rw [hGZ, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_mul] at e
  have h : (cT s M * cT s Z + cT s b * cT s C) * J * (Z * M + C * b) =
      cT s M * (cT s Z * J * Z) * M + cT s M * (cT s Z * J * C) * b +
        (cT s b * (cT s C * J * Z) * M + cT s b * (cT s C * J * C) * b) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  rw [h, hzz, hzc, hcz, hcc] at e
  simpa using e

theorem isUnit_of_form {A : Type} [CommRing A] (s : A →+* A) {m : ℕ} {J₀ M : Matrix (Fin m) (Fin m) A}
    (h : cT s M * J₀ * M = J₀) (hJ : IsUnit J₀.det) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hJ
  exact isUnit_of_mul_isUnit_right hJ

end GlobalTheory.SphEis.CoreIsom


open GlobalTheory.SphEis.CoreIsom in
theorem GlobalTheory.SphEis.core_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ (g₀ : GAd σ J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀).1 + adMat F C * b ∧ b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z ∧ (matHom _ σ J₀ g₀).1 = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z ∧ (g ∈ ratPts σ J → g₀ ∈ ratPts σ J₀) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  have hmap : ∀ {a b c d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin a) (Fin c) E)
      (W : Matrix (Fin c) (Fin d) E), cT (sigR (AF F) σ) (adMat F X) * adMat F Y * adMat F W =
        adMat F (cT (σ : E →+* E) X * Y * W) := by
    intro a b c d X Y W
    rw [adMat, adMat, adMat, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul]
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg
  have hCJ : adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
    have h1 : (matHom _ σ J g⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]
      conv_lhs => rw [← hgC]
      rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
    have h2 := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h2
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      ← Matrix.map_add _ (map_add _), hF.sum, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨M, hM⟩ : ∃ M, M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  have hZ : (matHom _ σ J g).1 * adMat F Z = adMat F Z * M + adMat F C * b := by
    calc (matHom _ σ J g).1 * adMat F Z = (adMat F C * adMat F (cT (σ : E →+* E) D * J) +
          adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + adMat F D * adMat F (cT (σ : E →+* E) C * J)) *
          ((matHom _ σ J g).1 * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = adMat F C * (adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F D * (adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 * adMat F Z) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = adMat F Z * M + adMat F C * b := by
        rw [hCJ, ← hM, ← hb]
        have h0 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by
          simp only [adMat]; rw [← Matrix.map_mul, hF.cz]; simp
        rw [h0, Matrix.mul_zero, add_zero, add_comm]
  have hG : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hMu : cT (sigR (AF F) σ) M * adMat F J₀ * M = adMat F J₀ :=
    unitary_core (sigR (AF F) σ) hG (by rw [hmap, hF.cz]; simp) (by rw [hmap, hF.zc]; simp)
      (by rw [hmap, hF.cc]; simp) (by rw [hmap, hF.zz]) hZ
  have hdet : IsUnit (adMat F J₀).det := by
    rw [adMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Ne.isUnit hF.herm₀.2).map _
  have hMU := isUnit_of_form _ hMu hdet
  let g₀ : GAd σ J₀ := ⟨hMU.unit, by
    show cT (sigR (AF F) σ) (hMU.unit : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) * adMat F J₀ * hMU.unit = adMat F J₀
    rw [hMU.unit_spec]; exact hMu⟩
  have hg₀ : (matHom _ σ J₀ g₀).1 = M := hMU.unit_spec
  refine ⟨g₀, b, ?_, hb, ?_, ?_⟩
  · rw [hg₀]; exact hZ
  · rw [hg₀]; exact hM
  · intro hr
    have hr' : (show HR (AF F) σ J from g).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (bc (inclR (F := F) (AF F))) := hr
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hr'
    have hGx : (matHom _ σ J g).1 = adMat F (x : Matrix (Fin n) (Fin n) E) := by
      exact (congrArg Units.val hxg).symm
    have hMM : M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) := by
      rw [hM, hGx]; simp only [adMat, Matrix.map_mul]
    have inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a c h =>
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) h
    have hM₀ : cT (σ : E →+* E) (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) * J₀ *
        (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) = J₀ := by
      apply Matrix.map_injective inj
      show adMat F _ = adMat F _
      rw [← hmap, ← hMM]; exact hMu
    have hM₀U := isUnit_of_form _ hM₀ (Ne.isUnit hF.herm₀.2)
    show (show HR (AF F) σ J₀ from g₀).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J₀).map (bc (inclR (F := F) (AF F)))
    refine Subgroup.mem_map.2 ⟨hM₀U.unit, ?_, Units.ext ?_⟩
    · show cT (σ : E →+* E) (hM₀U.unit : Matrix (Fin m) (Fin m) E) * J₀ * hM₀U.unit = J₀
      rw [hM₀U.unit_spec]; exact hM₀
    · show (hM₀U.unit : Matrix (Fin m) (Fin m) E).map (inclR (F := F) (AF F)) = (matHom _ σ J₀ g₀).1
      rw [hM₀U.unit_spec, hg₀, hMM]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped Classical

namespace GlobalTheory.PureFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulSupport_finite (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) : (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro i
    exact (x i).2.2
  refine Set.Finite.subset (Filter.eventually_cofinite.1 (hφ.and hx)) ?_
  intro v hv hv'
  apply hv
  obtain ⟨h1, h2⟩ := hv'
  simp only [h1]
  rw [Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h2)]
  rfl

theorem update_eventually (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∀ᶠ v in Filter.cofinite, Function.update φ v₁ g v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hφ, Filter.eventually_cofinite_ne v₁] with v hv hne
  rw [Function.update_of_ne hne]; exact hv

theorem finprod_update (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (g : (κ → Fv F v₁) → ℂ)
    (hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (x : κ → AF F) :
    (∏ᶠ v, Function.update φ v₁ g v fun i => evFin F v (x i)) =
      g (fun i => evFin F v₁ (x i)) * ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i) := by
  rw [← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ g hφ) x),
    ← mul_finprod_cond_ne v₁ (mulSupport_finite _ (update_eventually φ v₁ (fun _ => 1) hφ) x)]
  simp only [Function.update_self, one_mul]
  congr 1
  refine finprod_congr fun v => finprod_congr fun hv => ?_
  rw [Function.update_of_ne hv, Function.update_of_ne hv]

theorem comp_add_of_at (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z) (i : κ) :
    (z i).1 = 0 ∧ ∀ v, v ≠ v₁ → evFin F v (z i) = 0 := by
  set u : AF F := 1 - GlobalTheory.EmbChart.atPlace v₁ 1 with hu
  have h0 : evFin F v₁ u = 0 := by
    rw [hu, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 : (u * z i).1 = (z i).1 := by
      have : u.1 = 1 := by
        rw [hu]
        show (1 : Ainf F) - (0 : Ainf F) = 1
        exact sub_zero 1
      show u.1 * (z i).1 = (z i).1
      rw [this, one_mul]
    rw [← h1, hzi]; rfl
  · have h2 : evFin F v u = 1 := by
      rw [hu, map_sub, map_one]
      have : evFin F v (GlobalTheory.EmbChart.atPlace v₁ 1) = 0 := evalV_singleFin_ne hv 1
      rw [this, sub_zero]
    have := congrArg (evFin F v) hzi
    rwa [map_mul, h2, one_mul, map_zero] at this

end GlobalTheory.PureFactor


open GlobalTheory.PureFactor in
theorem GlobalTheory.PureFactor.exists_rest_factor : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∃ r : (κ → AF F) → ℂ, (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v₁) z → r (x + z) = r x) ∧
      ∀ ψ₀ : (κ → Fv F v₁) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v₁) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v₁ ψ₀) := by
  intro F _ _ κ _ v₁ f φ hφ
  refine ⟨fun x => f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) *
    ∏ᶠ v, Function.update φ v₁ (fun _ => 1) v fun i => evFin F v (x i), ?_, ?_⟩
  · intro x z hz
    have hI : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + z) i)) = fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i) := by
      funext i
      have h := (comp_add_of_at v₁ z hz i).1
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((x i).1 + (z i).1) = (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
      rw [h, add_zero]
    simp only
    rw [hI]
    congr 1
    refine finprod_congr fun v => ?_
    by_cases hv : v = v₁
    · subst hv; simp only [Function.update_self]
    · rw [Function.update_of_ne hv]
      congr 1
      funext i
      rw [Pi.add_apply, map_add (f := _), (comp_add_of_at v₁ z hz i).2 v hv, add_zero]
  · intro ψ₀
    funext x
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    rw [finprod_update φ v₁ ψ₀ hφ x]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlace
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem exists_isFockMapD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := _root_.GlobalTheory.CCRFock.fock_map_of_ccr_dep H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.FrameCompl

variable {E : Type} [Field E]

theorem cT_mul (τ : E →+* E) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add (τ : E →+* E) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i k; simp [cT]

theorem cT_cT (τ : E →+* E) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i k; simp [cT, hτ]

theorem cT_one (τ : E →+* E) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  ext i k; simp [cT, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cT_zero (τ : E →+* E) {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i k; simp [cT]

end GlobalTheory.SphEis.FrameCompl


open GlobalTheory.SphEis.FrameCompl in
theorem GlobalTheory.SphEis.exists_fr_of_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (j : ℕ) (C D : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) C * J * C = 0 → cT (σ : E →+* E) D * J * D = 0 → cT (σ : E →+* E) C * J * D = 1 → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ := by
  intro F E _ _ _ _ _ σ hcm n J hJ j C D hcc hdd hcd
  set τ : E →+* E := (σ : E →+* E) with hτdef
  have hτ : ∀ x, τ (τ x) = x := fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x
  have hJJ : cT τ J = J := by ext i k; exact hJ.1 i k
  have hdc : cT τ D * J * C = 1 := by
    have := congrArg (cT τ) hcd
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_one, ← Matrix.mul_assoc] at this

  let W : Submodule E (Fin n → E) :=
    LinearMap.ker (Matrix.toLin' (cT τ C * J)) ⊓ LinearMap.ker (Matrix.toLin' (cT τ D * J))
  let m := Module.finrank E W
  let b : Module.Basis (Fin m) E W := Module.finBasis E W
  let Z : Matrix (Fin n) (Fin m) E := Matrix.of fun r k => (b k : Fin n → E) r
  have hZv : ∀ u : Fin m → E, Z *ᵥ u = ((∑ k, u k • b k : W) : Fin n → E) := by
    intro u; ext r
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k, Z *ᵥ Pi.single k 1 = (b k : Fin n → E) := by
    intro k; rw [hZv]; simp [Pi.single_apply]
  have hCZ : cT τ C * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.1
  have hDZ : cT τ D * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.2
  have hZC : cT τ Z * J * C = 0 := by
    have := congrArg (cT τ) hCZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this
  have hZD : cT τ Z * J * D = 0 := by
    have := congrArg (cT τ) hDZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this

  set Pr : Matrix (Fin n) (Fin n) E := 1 - C * (cT τ D * J) - D * (cT τ C * J) with hPr
  have hCPr : cT τ C * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcc, hcd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hDPr : cT τ D * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hdc, hdd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hmem : ∀ i, Pr *ᵥ Pi.single i 1 ∈ W := by
    intro i
    refine ⟨?_, ?_⟩
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hCPr, Matrix.zero_mulVec]
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDPr, Matrix.zero_mulVec]
  let M : Matrix (Fin m) (Fin n) E := Matrix.of fun k i => b.repr ⟨_, hmem i⟩ k
  have hZM : Z * M = Pr := by
    apply Matrix.ext_of_mulVec_single; intro i
    rw [← Matrix.mulVec_mulVec]
    have : M *ᵥ Pi.single i 1 = fun k => b.repr ⟨_, hmem i⟩ k := by
      ext k; simp [M, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hZv, b.sum_repr]
  have hdec : C * (cT τ D * J) + D * (cT τ C * J) + Z * M = 1 := by
    rw [hZM, hPr]; abel

  set J₀ : Matrix (Fin m) (Fin m) E := cT τ Z * J * Z with hJ₀
  have hJ₀h : cT τ J₀ = J₀ := by
    rw [hJ₀, cT_mul, cT_mul, cT_cT τ hτ, hJJ, Matrix.mul_assoc]
  have hCZ' : cT τ C * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hCZ
  have hDZ' : cT τ D * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hDZ
  have key : J * Z = cT τ M * J₀ := by
    have h1 : cT τ (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) = 1 := by rw [hdec, cT_one]
    rw [cT_add, cT_add, cT_mul, cT_mul, cT_mul, cT_mul, cT_mul, cT_cT τ hτ, cT_cT τ hτ, hJJ] at h1
    conv_lhs => rw [← Matrix.one_mul (J * Z), ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', Matrix.mul_zero, zero_add, hJ₀]
  have hdet : J₀.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hJz : J *ᵥ (Z *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hJz
    rw [hZv] at hz
    have hs : (∑ k, u k • b k : W) = 0 := Subtype.ext hz
    exact hu0 (funext fun k => Fintype.linearIndependent_iff.mp b.linearIndependent u hs k)
  have hinv : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul J₀ (isUnit_iff_ne_zero.mpr hdet)
  set S : Matrix (Fin n) (Fin n) E := C * (cT τ D * J) + Z * (J₀⁻¹ * (cT τ Z * J)) + D * (cT τ C * J) with hS
  have a1 : cT τ D * (J * C) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hdc
  have a2 : cT τ Z * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZC
  have a3 : cT τ C * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hcc
  have a4 : cT τ D * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hdd
  have a5 : cT τ Z * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZD
  have a6 : cT τ C * (J * D) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hcd
  have a7 : cT τ Z * (J * Z) = J₀ := (Matrix.mul_assoc _ _ _).symm
  have hSC : S * C = C := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a1, a2, a3, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have hSD : S * D = D := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a4, a5, a6, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hSZ : S * Z = Z := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', a7, Matrix.mul_zero, add_zero, zero_add]
    rw [hinv, Matrix.mul_one]
  have hS1 : S = 1 := by
    calc S = S * (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) := by rw [hdec, Matrix.mul_one]
      _ = S * C * (cT τ D * J) + S * D * (cT τ C * J) + S * Z * M := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 1 := by rw [hSC, hSD, hSZ, hdec]
  have hdim : m + 2 * j = n := by
    have ht := congrArg Matrix.trace hS1
    rw [hS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm C, Matrix.trace_mul_comm Z,
      Matrix.trace_mul_comm D] at ht
    simp only [Matrix.mul_assoc, a1, a6, a7, hinv, Matrix.trace_one, Fintype.card_fin] at ht
    have : ((m + 2 * j : ℕ) : E) = (n : E) := by push_cast; rw [← ht]; ring
    exact_mod_cast this
  refine ⟨m, Z, J₀, hcm, hJ, ⟨fun i k => ?_, hdet⟩, hcc, hdd, hcd, hdc, hCZ, hDZ, hZC, hZD, rfl, hS1, hdim⟩
  have := congrFun (congrFun hJ₀h i) k
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorMoveArgsOriginEqBoxIndicatorStatement
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup), (∀ j, g (G.m, j) = colDiag G ϖ a a' j) → ∀ e : Vars G, Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  first | exact @GlobalTheory.OriginBox.indicator_moveArgs_origin | exact GlobalTheory.OriginBox.indicator_moveArgs_origin | (intros; apply GlobalTheory.OriginBox.indicator_moveArgs_origin <;> assumption)
end

