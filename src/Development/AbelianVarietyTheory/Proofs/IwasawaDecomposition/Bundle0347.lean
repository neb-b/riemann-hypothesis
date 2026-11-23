module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type} [CommGroup M]
    (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ),
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) →
    (∀ u u' : 𝓞 E, u ∉ P.asIdeal → u' ∉ P.asIdeal → NX.tameVal φ P e (u * u') = NX.tameVal φ P e u * NX.tameVal φ P e u') ∧
    ∀ u u' : 𝓞 E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal φ P e u = NX.tameVal φ P e u' := by
  first | exact @GlobalTheory.TameValChar.main | exact GlobalTheory.TameValChar.main | (intros; apply GlobalTheory.TameValChar.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToMapSurj
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.BaseEnl

open GlobalTheory.Mem.BaseExt

section map

variable {L L' : Type} [Field L] [Field L'] [CharZero L] [CharZero L'] (ι : L →ₐ[ℚ] L')
  (K : IntermediateField ℚ L)

def toMap : K →+* K.map ι := (K.equivMap ι).toRingEquiv.toRingHom

theorem coe_toMap (x : K) : (toMap ι K x : L') = ι x := rfl

theorem toMap_surj : Function.Surjective (toMap ι K) := (K.equivMap ι).surjective

theorem image_map {E : Type} [Field E] (𝔞 : Ideal (𝓞 E)) (e : E → L) :
    extend (toMap ι K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : L) = e (a : E)}) =
      Submodule.span (𝓞 (K.map ι)) {x : K.map ι | ∃ a ∈ 𝔞, (x : L') = ι (e (a : E))} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, by rw [coe_toMap, hy]⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨y, rfl⟩ := toMap_surj ι K x
    exact ⟨y, ⟨a, ha, ι.injective hx⟩, rfl⟩

end map

theorem exists_enl : ∀ (B : Base) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) →
    ∃ B' : Base, Enl B B' ∧ ∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S h
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.LL
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (S ∪ SE) (by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [h z hz, hSE z hz])
  have hEK := hE K (fun z hz => hS z (Finset.mem_union_right _ hz)) B.embLL
  have : NumberField K := {}
  let ι : B.LL →ₐ[ℚ] K := (B.embLL.codRestrict K hEK).toRatAlgHom
  have hι : ∀ x, K.val (ι x) = B.embLL x := fun _ => rfl
  have tr : ∀ (F : IntermediateField ℚ B.LL) (w : ℂ), (∃ z ∈ F, B.embLL z = w) →
      ∃ z ∈ F.map ι, K.val z = w := by
    rintro F w ⟨z, hz, rfl⟩
    exact ⟨ι z, ⟨z, hz, rfl⟩, rfl⟩
  have im : ∀ F : IntermediateField ℚ B.LL,
      (K.val : K →+* ℂ) '' (F.map ι : Set K) = B.embLL '' (F : Set B.LL) := by
    intro F
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · exact tr F w
  have hg0 := B.coeffGaloisSubfield_isGalois
  let f := toMap ι B.Ks
  refine ⟨{ toPre := B.toPre
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := (ι : B.LL →+* K).comp B.embE
            embE_φ₀ := by rw [← B.embE_φ₀]; rfl
            LL0 := B.LL0.map ι
            coeffGaloisSubfield_isGalois := @IsGalois.of_algEquiv ℚ B.LL0 _ _ (B.LL0.map ι) _ _ _ hg0 (B.LL0.equivMap ι)
            Ks := B.Ks.map ι
            Ks_le := IntermediateField.map_mono ι B.Ks_le
            E_le_Ks := fun x => ⟨B.embE x, B.E_le_Ks x, rfl⟩
            roots_Ks := fun N hN => tr _ _ (B.roots_Ks N hN)
            roots_Ks' := fun N hN => tr _ _ (B.roots_Ks' N hN)
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := tr _ _ B.rootOfUnity_eightQ_mem_coeffGaloisSubfield
            roots_LL := fun u => ?_ }, ⟨rfl, im _, im _, ?_⟩, ?_⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := B.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_map ι B.Ks 𝔞 B.embE)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := B.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g a))
    have e2 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g (B.host.conj a)))
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · obtain ⟨z, hz⟩ := B.roots_LL u
    exact ⟨ι z, hz⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (Finset.mem_union_left _ hz)⟩, rfl⟩

end GlobalTheory.Mem.BaseEnl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice : ∀ (D : _root_.Formalism.BasicNotions.D7) (c : _root_.Formalism.BasicNotions.NChoice D),
    _root_.Formalism.BasicNotions.NChTie D c → IsGalois ℚ ↥D.LL0 →
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (c.twI w) := by
  intro D c hc hG w hw
  unfold _root_.Formalism.BasicNotions.NTw.NonzeroIndexPlace
  refine ⟨if c.sd w = true then w else D.what₂.places.conj w, ?_, ?_⟩
  · split_ifs
    · exact hw
    · rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]
      exact hw
  · have h := _root_.GlobalTheory.TwistGoodCompare.liesUnder_of_tie hG hc w
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder at h
    exact h

end GlobalTheory.Mem.Top
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOnto
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF

theorem conjAL_includeLeft {L : Type} [Field L] [NumberField L] [IsCMField L] (x : L) :
    conjAL L ((Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) x) =
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) ((IsCMField.complexConj L : L →+* L) x) := by
  simp [conjAL, Algebra.TensorProduct.map_tmul]

theorem incGL_mem_GA {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (γ₀ : GL (Fin n) L)
    (h : γ₀ ∈ GQ0 L n) : incGL (L := L) (n := n) γ₀ ∈ GA L n := by
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := h
  show ((incGL (L := L) (n := n) γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
    conjT (conjAL L) (incGL (L := L) (n := n) γ₀) = 1
  have hc : conjT (conjAL L)
      ((incGL (L := L) (n := n) γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := by
    ext i j
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply, incGL,
      Matrix.GeneralLinearGroup.map_apply]
    exact conjAL_includeLeft _
  rw [hc]
  have e : ((incGL (L := L) (n := n) γ₀ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) := rfl
  rw [e, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]

theorem ratHom_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L),
    γ₀ ∈ GQ0 L n → ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom (L := L) (n := n) γ = γ₀ := by
  intro L _ _ _ n γ₀ h
  let g : GA L n := ⟨incGL (L := L) (n := n) γ₀, incGL_mem_GA γ₀ h⟩
  have hg : g ∈ GQ L n := Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ₀, h, rfl⟩)
  refine ⟨⟨g, hg⟩, ?_⟩
  apply incGL_injective
  exact incGL_ratFun (L := L) (n := n) ⟨g, hg⟩

end GlobalTheory.AlgWtF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertAll

theorem nonSplitAt_of_forall (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (hε : IsPlaceIdem D v ε)
    (hns : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) : GlobalTheory.WeilParts.NonSplitAt D v ε := by
  refine ⟨hε, fun ⟨e, he, heq⟩ => ?_⟩
  have k := hns e he
  have e0 : e = 0 := by
    rw [← heq, mul_add, he.1, he.2.1, add_zero] at k
    exact k
  rw [e0, map_zero, zero_add] at heq
  obtain ⟨α, rfl, h1, -⟩ := hε
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have : pairA D.host.F 0 α = 0 := hinj (by rw [map_zero]; exact heq.symm)
  have : α = 0 := congrArg Prod.snd this
  rw [this, map_zero] at h1
  exact zero_ne_one h1

theorem unramAt_of_unrAtV (D : D7) (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) (hχ : Formalism.IndefR.WeilFull.UnrAtV ε χ) : GlobalTheory.WeilParts.UnramAt ε χ :=
  fun x hx i1 i2 => hχ x (by linear_combination (-1 : AE D) * hx) i1 i2

theorem inertAllO_of_eta (D : D7) (hη : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) : Formalism.IndefR.WeilFull.InertAllO D := by
  intro ψ S T χS χT om H _ _ ΛS ΛT hS hT βS βT hβS hβT v ε hε _ hns uS uT g h sg sh hg hh f hf hvac
  have hv : GlobalTheory.WeilParts.NonSplitAt D v ε := nonSplitAt_of_forall D v ε hε hns
  have hst : ∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) ↔
      actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v) :=
    fun u => GlobalTheory.LatStab.mem_latO_iff_actO_mem D S T ΛS ΛT βS βT hS.1 hT.1 hβS hβT g h hg hh _ u
  have hfix : ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun w => w = v),
      heisO ψ S T u f = f := by
    intro u hu
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2
  exact _root_.GlobalTheory.VacInert.fixesVacAt_of_unram D ψ H.std S T ΛS ΛT hS hT χS χT om hη H v ε hv (unramAt_of_unrAtV D ε χS uS) (unramAt_of_unrAtV D ε χT uT) g h sg sh hst f hf hfix

theorem inertAllO : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D :=
  fun D => inertAllO_of_eta D (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D)

end GlobalTheory.InertAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompactAction

theorem trace_Jm {n p q : ℕ} (h : p + q = n) (ε : Fin n → Bool) (hε : ∀ a, ε a = decide ((a : ℕ) < p)) :
    (Formalism.REAL.Jm ε).trace = (p : ℂ) - q := by
  subst h
  unfold Formalism.REAL.Jm
  rw [Matrix.trace_diagonal, Fin.sum_univ_add]
  simp [hε, sub_eq_add_neg]

theorem isCartanInv_one {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have hu : IsUnit B := IsUnit.of_mul_eq_one _ hB
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, hB, Matrix.conjTranspose_one]
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hi]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  exact (Matrix.isUnit_nonsing_inv_iff).2 hu

theorem conj_unitary {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hg : gᴴ * G * g = G) :
    B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have h0 : B * B⁻¹ = 1 := by rw [hi, hB]
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h0, Matrix.conjTranspose_one]
  have hG : (B⁻¹)ᴴ * B⁻¹ = G := by
    calc _ = (B⁻¹)ᴴ * (Bᴴ * G) := by rw [← hi]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Bᴴ * (gᴴ * ((B⁻¹)ᴴ * B⁻¹) * g) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, hg, h]

theorem det_conj {n : ℕ} {F F' : Matrix (Fin n) (Fin n) ℂ} (h : F' * F = 1) (A C x : Matrix (Fin n) (Fin n) ℂ) :
    (A * (F * x * F') + C).det = (F' * A * F * x + F' * C * F).det := by
  have e : F' * A * F * x + F' * C * F = F' * (A * (F * x * F') + C) * F := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h, Matrix.mul_one]
  have hd : F'.det * F.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  rw [e, Matrix.det_mul, Matrix.det_mul]
  linear_combination (-(A * (F * x * F') + C).det) * hd

theorem pureTensorO_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (c : ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
  have hd : ∀ τ z (f : WO S T → ℂ), dRho (heisO ψ S T) θ τ z (c • f) = c • dRho (heisO ψ S T) θ τ z f := by
    intro τ z f
    funext x
    simp only [Formalism.IndefR.Datum.dRho, heisO, Pi.smul_apply, smul_eq_mul]
    rw [← deriv_const_mul_field]
    congr 1
    funext t
    ring
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) _ _ (c • (1 : Module.End ℂ (WO S T → ℂ))) (fun k f _ => ⟨trivial, ?_⟩) f trivial P).2.symm
  simp only [aPlusAll, Formalism.IndefR.Datum.aPlus, crea, LinearMap.smul_apply, Module.End.one_apply, hd]
  rw [smul_comm Complex.I c, ← smul_sub, smul_comm]

theorem om_pureTensorO_eq_fact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  intro D ψ θ S T χS χT om Sp M BS hom hθ hS hT hBS p q hpq hε a b ha hb x₁ x₂ x₃ h₁ h₂ h₃ f hf hv g hg h hh hk
  have hu : ∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ :=
    fun τ => conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S g τ)
  refine ⟨hu, fun P => ?_⟩
  have f1 : ∀ τ, M.fr τ * (M.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have f2 : ∀ τ, (M.fr τ)⁻¹ * M.fr τ = 1 := fun τ => mul_eq_one_comm.1 (f1 τ)
  have b1 : ∀ τ, BS τ * (BS τ)⁻¹ = 1 := fun τ => by
    have hB : BS τ * ((BS τ)ᴴ * gramAt D S τ) = 1 := mul_eq_one_comm.1 (hBS τ)
    rw [Matrix.inv_eq_right_inv hB, hB]
  have hc : ∀ τ, cart M τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * cart M τ := fun τ => by
    have e := congrArg (fun X => (M.fr τ)⁻¹ * X * M.fr τ) (hk τ).2
    simp only [Matrix.mul_assoc, f2, Matrix.mul_one] at e
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), f2, Matrix.one_mul] at e
    unfold cart
    simp only [Matrix.mul_assoc]
    exact e.symm
  have htr : ∀ τ, (cart M τ).trace = (p τ : ℂ) - q τ := fun τ => by
    unfold cart
    rw [Matrix.trace_mul_cycle, f1, Matrix.one_mul, trace_Jm (hpq τ) _ (hε τ)]
  have hvac := _root_.GlobalTheory.VacuumCharacter.vacuum_character D ψ θ S T χS χT om hom hθ hS hT (cart M) (fun τ => isCartanInv_one (hBS τ))
    (GlobalTheory.Chain.VacVec.cart_isCartanInv M) a b ha hb x₁ x₂ x₃ h₁ h₂ (fun τ => by
      rw [htr]
      have := congrArg (fun x : ℚ => (x : ℂ)) (h₃ τ)
      push_cast at this
      exact this) f hf hv g hg h hh hc
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ (fun _ => 1) (fun _ => 1) BS
    (fun τ => BS τ * ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ)) (cart M) (cart M) (onb M)
    (fun τ => onb M τ * (M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹)) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) hc
    (fun τ => by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, b1, Matrix.one_mul])
    (fun τ => by unfold onb; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, f2, Matrix.one_mul]) f hf P).2,
    _root_.GlobalTheory.FockBasis.pureTensorO_basis D ψ θ S T Sp M BS hom.std hθ hBS _ _ hk hu _ (hom.om_pres _ _ hf), hvac, pureTensorO_smul]
  unfold fact
  rw [LinearMap.smul_apply, map_smul]
  congr 1
  unfold fchar
  refine Finset.prod_congr rfl fun τ _ => ?_
  have eP : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 + cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, f2]; rfl
  have eM : (M.fr τ)⁻¹ * ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm (M.ε τ))) * M.fr τ = (1 / 2 : ℂ) • (1 - cart M τ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, f2]; rfl
  have eU : ((BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ).det = (compAt θ τ (Formalism.L2.Theta.mt S g)).det := by
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc, b1, Matrix.one_mul]
  unfold detP detM
  rw [det_conj (f2 τ), det_conj (f2 τ), eP, eM, eU]

end GlobalTheory.FockCompactAction

end
end

