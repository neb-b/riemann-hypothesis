module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0443
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatLevel

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_nsmul_smul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n)))
    (y : Mx D m n) : ∃ N : ℕ, 0 < N ∧ ∀ α ∈ intAf D.host.F,
      N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) ∈ U := by
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 α :=
    continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, fun α hα => ?_⟩
  have h1 : φ (N • α) ∈ U := h α hα
  have h2 : φ (N • α) = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • y) := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • α) = N • pairA D.host.F 0 α :=
      Prod.ext (show (0 : Ainf D.host.F) = N • 0 by rw [smul_zero]) rfl
    show pairA D.host.F 0 (N • α) • y i j = N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * y i j)
    rw [e1, smul_assoc, Algebra.smul_def (pairA D.host.F 0 α)]
  rwa [h2] at h1

def actHom (S T : HSp D) (g : GA D S) (h : GA D T) : WO S T →+ WO S T :=
  AddMonoidHom.mk' (actO S T g h) fun x y => by
    unfold actO
    rw [Matrix.mul_add, Matrix.add_mul]

theorem continuous_actO (S T : HSp D) (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [actO, Matrix.mul_apply]
  refine continuous_finsetSum _ fun k _ => Continuous.mul (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ?_) continuous_const
  exact (continuous_apply k).comp (continuous_apply l)

theorem actO_map_inf (S T : HSp D) (g : GA D S) (h : GA D T) {u : WO S T} (hu : u.map (infPart D) = 0) :
    (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

def finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) : AddSubgroup (Mx D m n) :=
  (L.map (finPart D).toAddMonoidHom.mapMatrix).comap (finPart D).toAddMonoidHom.mapMatrix

theorem mem_finSat {m n : ℕ} (L : AddSubgroup (Mx D m n)) (x : Mx D m n) :
    x ∈ finSat L ↔ ∃ l ∈ L, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 := by
  have key : ∀ l : Mx D m n, Matrix.map (x - (1 : ℕ) • l) (finPart D) = 0 ↔
      (finPart D).toAddMonoidHom.mapMatrix l = (finPart D).toAddMonoidHom.mapMatrix x := by
    intro l
    rw [one_smul, eq_comm (b := (finPart D).toAddMonoidHom.mapMatrix x), ← sub_eq_zero (a := (finPart D).toAddMonoidHom.mapMatrix x), ← map_sub]
    rfl
  simp only [key]
  rfl

theorem level_of_generators : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • u ∈ U) ∧ ∀ (g : GA D S) (h : GA D T), ∃ N : ℕ, 0 < N ∧ ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), N • actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT ⟨G, hG, _, hgen⟩
  have h1 : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ N : ℕ, 0 < N ∧
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        N • u ∈ U := by
    intro U hU
    choose M hM hMU using fun y : WO S T => exists_nsmul_smul_mem U hU y
    refine ⟨∏ y ∈ hG.toFinset, M y, Finset.prod_pos fun y _ => hM y, ?_⟩
    refine hgen (U.comap (nsmulAddMonoidHom (∏ y ∈ hG.toFinset, M y))) fun α hα u hu => ?_
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem M (hG.mem_toFinset.2 hu)
    show (∏ y ∈ hG.toFinset, M y) • _ ∈ U
    rw [hc, mul_comm, mul_smul]
    exact U.nsmul_mem (hMU u α hα) c
  refine ⟨h1, fun g h => ?_⟩
  have hop : IsOpen (finSat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) : Set (WO S T)) := by
    convert GlobalTheory.LatOpen.isOpen_nsmul_latO D S T ΛS ΛT hS hT 1 one_pos using 1
    exact Set.ext fun x => mem_finSat _ x
  obtain ⟨N, hN, hNU⟩ := h1 ((finSat _).comap (actHom S T g h)) (hop.preimage (continuous_actO S T g h))
  refine ⟨N, hN, fun u hu => ?_⟩
  have h2 : actHom S T g h (N • u) ∈ finSat _ := hNU u hu
  obtain ⟨l, hl, hl0⟩ := (mem_finSat _ _).1 h2
  have h3 : (actHom S T g h (N • u)).map (infPart D) = 0 :=
    actO_map_inf S T g h (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  have h4 := latO_fin hl
  have h5 : actHom S T g h (N • u) = l := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · exact (congrFun (congrFun h3 i) j).trans (congrFun (congrFun h4 i) j).symm
    · have h6 : finPart D (actHom S T g h (N • u) i j - (1 : ℕ) • l i j) = 0 := congrFun (congrFun hl0 i) j
      rwa [one_smul, RingHom.map_sub, sub_eq_zero] at h6
  rw [map_nsmul] at h5
  exact h5 ▸ hl

end GlobalTheory.LatLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjToricPeriodCoordinateSumOverClasses
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ConjCoordToric

theorem lamF_mul {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y y' : (Af E)ˣ) :
    lamF s χ (y * y') = lamF s χ y * lamF s χ y' := by
  unfold lamF
  rw [map_mul, Units.val_mul, IdeleModule.modF_mul, mul_pow]
  push_cast
  ring

theorem coordIn_eq_mul {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold GlobalTheory.ToricTransport.coordIn
  ring

theorem exists_latSum {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E))
    (h : ∀ q : PicO c, ∃ S, IsLatSum φ (2 * s) κ (lattice c q.out) S) (y : (Af E)ˣ) :
    ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : PicO c, q = QuotientGroup.mk y := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := h q
  have hq' : (QuotientGroup.mk q.out : PicO c) = QuotientGroup.mk y := by rw [QuotientGroup.out_eq', hq]
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq')
  have hy : y = Units.map (algebraMap E (Af E)).toMonoidHom α * q.out * u := by
    have : y = q.out * (Units.map (algebraMap E (Af E)).toMonoidHom α * u) := by rw [hau]; group
    rw [this]
    ac_rfl
  rw [hy, GlobalTheory.ClassInv.lattice_princ_mul_unit _ α hu]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).1⟩

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  intro hC K _ _ d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hE hφ hφK s hs κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  classical
  obtain ⟨hAux, hVal, -, S, hS, rfl⟩ := hV
  obtain ⟨⟨hlam, hInf'⟩, hfin', S'', hS'', rfl⟩ := hV'
  haveI : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  have hunit' : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ' u = 1 := by
    intro u hu
    have h1 : lamF s χ' u = 1 := by
      rw [hlam]
      unfold lamF
      rw [GlobalTheory.ClassInv.finPart_unit hVal hu, ObjModel.modF_unit hu]
      simp
    unfold lamF at h1
    rw [ObjModel.modF_unit hu] at h1
    simp at h1
    exact h1
  have hex : ∀ q : PicO (condQ 𝔣 Q), ∃ S', IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (q.out * (upIdele K E t)⁻¹)) S' :=
    fun q => exists_latSum hφ s κ' (condQ 𝔣 Q) (fun q => ⟨S'' q, hS'' q⟩) _
  choose S' hS' using hex
  have hLC : ∀ q : PicO (condQ 𝔣 Q), g (coordIn E d s κ Ω₀ 1 * S q 0) =
      coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0) := fun q => by
    rw [← coordIn_eq_mul, ← coordIn_eq_mul]
    exact hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hAux⟩ κ κ' hκ' q.out (S q) (S' q)
      (hS q) (hS' q)
  have hCI : ∀ q : PicO (condQ 𝔣 Q), (lamF s χ' (q.out * (upIdele K E t)⁻¹))⁻¹ * S' q 0 =
      (lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0 := by
    intro q
    refine GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hInf' hunit' _ _ (S' q) (S'' _) ?_
      (hS' q) (hS'' _)
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  have hsum : ∀ (ψ : HChar E) (R : PicO (condQ 𝔣 Q) → ℂ → ℂ),
      (∑ᶠ q : PicO (condQ 𝔣 Q), ((finPart ψ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * R q 0) =
        ∑ q, (lamF s ψ q.out)⁻¹ * R q 0 := fun ψ R => by
    rw [finsum_eq_sum_of_fintype]
    rfl
  rw [hsum, hsum, coordIn_eq_mul (E := E) d s κ Ω₀, coordIn_eq_mul (E := E) d s κ Ω₁]
  calc g (coordIn E d s κ Ω₀ 1 * ∑ q, (lamF s χ q.out)⁻¹ * S q 0)
      = ∑ q, (g (lamF s χ q.out))⁻¹ * g (coordIn E d s κ Ω₀ 1 * S q 0) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [show coordIn E d s κ Ω₀ 1 * ((lamF s χ q.out)⁻¹ * S q 0) =
          (lamF s χ q.out)⁻¹ * (coordIn E d s κ Ω₀ 1 * S q 0) by ring, map_mul, map_inv₀]
    _ = ∑ q, (lamF s χ' q.out)⁻¹ * (coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hlam, hLC]
    _ = ∑ q, coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ((lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← hCI q]
        have hm : lamF s χ' q.out = lamF s χ' (q.out * (upIdele K E t)⁻¹) * lamF s χ' (upIdele K E t) := by
          rw [← lamF_mul, inv_mul_cancel_right]
        rw [hm, mul_inv]
        ring
    _ = coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ∑ q, (lamF s χ' q.out)⁻¹ * S'' q 0 := by
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (upIdele K E t)⁻¹ : PicO (condQ 𝔣 Q))) _ _ fun q => rfl
    _ = _ := by ring

end GlobalTheory.ConjCoordToric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

def conjMap (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) : MMap M' where
  toFun v' := star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩)
  map_update_add' v' i x y := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e, e, ← star_add, ← T.map_update_add]
    congr 3
    ext; simp
  map_update_smul' v' i a x := by
    have e : ∀ z : M'.sm i, (fun τ => (⟨c τ (Function.update v' i z τ), (h τ _).1 (Function.update v' i z τ).2⟩ : M.sm τ)) =
        Function.update (fun τ => (⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩ : M.sm τ)) i ⟨c i z, (h i _).1 z.2⟩ := by
      intro z
      funext τ
      by_cases hτ : τ = i
      · subst hτ; simp
      · simp [Function.update_of_ne hτ]
    rw [e, e]
    have e2 : (⟨c i ((a • x : M'.sm i) : M'.H i), (h i _).1 (a • x).2⟩ : M.sm i) = star a • ⟨c i x, (h i _).1 x.2⟩ := by
      ext; exact (c i).map_smulₛₗ a x
    rw [e2, T.map_update_smul, star_smul]
    simp only [RingHom.id_apply, star_star]

theorem conjMap_apply (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (v' : M'.Vec) :
    conjMap M M' c h T v' = star (T fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) := rfl

theorem conjMap_eq_zero (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T : MMap M) (hT : conjMap M M' c h T = 0) : T = 0 := by
  refine MultilinearMap.ext fun v => ?_
  have h1 := congrArg (fun U : MMap M' => U fun τ => ⟨(c τ).symm (v τ), (h τ _).2 (by simpa using (v τ).2)⟩) hT
  simp only [conjMap_apply, LinearIsometryEquiv.apply_symm_apply, Subtype.coe_eta, MultilinearMap.zero_apply,
    star_eq_zero] at h1
  exact h1

theorem mult_congr (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {J : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (hχ : ∀ k ∈ J, χ' k = χ k) {T : MMap M} (hT : T ∈ Mult θ M J χ) : T ∈ Mult θ M J χ' := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k hk g, hT.equiv, hT.cont⟩

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type}
    (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg Sg' : Pl0 → ℂ[X])
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ))
    (hS : ∀ P k, (Sg' P).coeff k = star ((Sg P).coeff k)) :
    Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) ≤
      Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
  obtain ⟨h, hM⟩ := _root_.GlobalTheory.ConjMult.conj_mult θ M M' c hc
  have key : ∀ T ∈ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)),
      conjMap M M' c h T ∈ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
    · simp only [hPart, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at h3 ⊢
      intro P hP k hk α hα R hR
      have h4 := sub_eq_zero.1 (h3 P hP k hk α hα R hR)
      refine sub_eq_zero.2 (MultilinearMap.ext fun v' => funext fun g => ?_)
      have h5 : ∑ γ ∈ R, T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ) =
          ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g :=
        congrArg (fun U : MMap M => U (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g) h4
      show ∑ γ ∈ R, star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (g * γ)) =
          ((Sg' P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * star (T (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) g)
      rw [← star_sum, h5, hS]
      simp
  let j : (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) →+
      (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q Sg' : Submodule ℂ (MMap M')) :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (J0 : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (goodPart θ M J χ e ⊓ hPart M J0 ok pl q Sg : Submodule ℂ (MMap M)) = Module.rank ℂ (goodPart θ M' J χ' e' ⊓ hPart M' J0 ok pl q (fun P => (Sg P).map (starRingEnd ℂ)) : Submodule ℂ (MMap M')) := by
  intro D V S S' θ M M' c hc J χ χ' e e' J0 Pl0 ok pl q Sg hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' J0 ok pl q Sg _ hχ he fun P k => by simp) ?_
  refine rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e J0 ok pl q _ Sg ?_ ?_ ?_
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]
  · intro P k
    simp

end GlobalTheory.ConjDim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantsMonomialApproximation
section
open scoped Classical

namespace GlobalTheory.FinTrace

noncomputable def dcToOrbit (G : Type) [Group G] (H K : Subgroup G) :
    DoubleCoset.Quotient (H : Set G) (K : Set G) → MulAction.orbitRel.Quotient H (G ⧸ K) :=
  Quotient.lift (fun g : G => (Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) : MulAction.orbitRel.Quotient H (G ⧸ K)))
    (by
      intro a b hab
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hab
      apply Quotient.sound
      show _ ∈ MulAction.orbit H _
      refine ⟨⟨h⁻¹, H.inv_mem hh⟩, ?_⟩
      show ((h⁻¹ : G) • (QuotientGroup.mk (h * a * k) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa [mul_assoc] using hk)

theorem dcToOrbit_mk (G : Type) [Group G] (H K : Subgroup G) (g : G) :
    dcToOrbit G H K (Quotient.mk _ g) = Quotient.mk _ (QuotientGroup.mk g : G ⧸ K) := rfl

theorem dcToOrbit_bijective (G : Type) [Group G] (H K : Subgroup G) :
    Function.Bijective (dcToOrbit G H K) := by
  constructor
  · intro q₁ q₂ he
    induction q₁ using Quotient.inductionOn with | h a => ?_
    induction q₂ using Quotient.inductionOn with | h b => ?_
    rw [dcToOrbit_mk, dcToOrbit_mk] at he
    obtain ⟨h, hh⟩ := Quotient.exact he
    change ((h : G) • (QuotientGroup.mk b : G ⧸ K)) = _ at hh
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hh
    apply Quotient.sound
    apply DoubleCoset.rel_iff.2
    refine ⟨(h : G)⁻¹, H.inv_mem h.2, ((h * b)⁻¹ * a)⁻¹, K.inv_mem hh, ?_⟩
    group
  · intro o
    induction o using Quotient.inductionOn with | h x => ?_
    induction x using QuotientGroup.induction_on with | H g => ?_
    exact ⟨Quotient.mk _ g, rfl⟩

theorem sum_doubleCoset_eq_sum_orbit : ∀ (G : Type) [Group G] (H K : Subgroup G) (F : G ⧸ K → ℂ), (∀ h : H, ∀ x : G ⧸ K, F (h • x) = F x) →
    ∑ᶠ q : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (1 / (Nat.card (GlobalTheory.LKLoc.locPart H K (Quotient.out q)) : ℂ)) * F (QuotientGroup.mk (Quotient.out q)) =
      ∑ᶠ a : MulAction.orbitRel.Quotient H (G ⧸ K),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * F (Quotient.out a) := by
  intro G _ H K F hF
  let e := Equiv.ofBijective _ (dcToOrbit_bijective G H K)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  have heq : e q = Quotient.mk _ (QuotientGroup.mk (Quotient.out q) : G ⧸ K) := by
    show dcToOrbit G H K q = _
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hrel : MulAction.orbitRel H (G ⧸ K) (Quotient.out (e q)) (QuotientGroup.mk (Quotient.out q)) := by
    apply Quotient.exact
    rw [Quotient.out_eq, heq]
  obtain ⟨h, hh⟩ := hrel
  rw [← hh, hF]
  congr 2
  have h1 := Nat.card_congr (Classical.choice (stabilizer_equiv_locPart G H K (Quotient.out q)))
  rw [← h1]
  exact_mod_cast (Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel (G := H) (a := h • (QuotientGroup.mk (Quotient.out q) : G ⧸ K))
    (b := (QuotientGroup.mk (Quotient.out q) : G ⧸ K)) (MulAction.orbitRel_apply.2 ⟨h, rfl⟩)).toEquiv).symm
end GlobalTheory.FinTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceExtensionByZeroTensorOfPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.ExtZero

open GlobalTheory.CompanionTheory.SaGen

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (x : K) (e : E) :
    iB (E := E) P (x ⊗ₜ[F] e) = P.inj x ⊗ₜ[F] e := rfl

theorem iB_eq_sum [FiniteDimensional F E] (P : PlaceMap F K) (y : K ⊗[F] E) :
    iB (E := E) P y = ∑ k, P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
      ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := by
  set B := Algebra.TensorProduct.basis K (Module.finBasis F E)
  conv_lhs => rw [← B.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, iB_tmul]

theorem continuous_iB [FiniteDimensional F E] [IsTopologicalRing K] (P : PlaceMap F K) :
    Continuous (iB (E := E) P) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
  have hc : ∀ k, Continuous fun y : K ⊗[F] E =>
      (Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k := fun k =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis K (Module.finBasis F E)).coord k)
  have h : (iB (E := E) P : K ⊗[F] E → AF F ⊗[F] E) = fun y => ∑ k,
      P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
        ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := funext (iB_eq_sum P)
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    Continuous.smul (f := fun y => P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k))
      (g := fun _ => (1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) (P.cont_inj.comp (hc k)) continuous_const

end GlobalTheory.CompanionTheory.SaGen.ExtZero

theorem GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) :=
  fun P => GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB P
end
end

