module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSympNegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedExtensionFinite
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

namespace GlobalTheory.TorusPart

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  refine ⟨?_⟩
  rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPair
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussFockPair

open GlobalTheory.GaussFockJ

def tensC {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)

theorem tensC_zero_left {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (y : Matrix (Fin n) (Fin d) ℂ) :
    tensC JX JW 0 y = 0 := by
  simp [tensC]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pair_Psi {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M u).1 (Psi M v).2 -
                 GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M v).1 (Psi M u).2 =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) u v)) := by
  have hform := M.co.form u v
  simp only [cA, incM] at hform
  rw [hform, ← evIHom_apply, map_sub, map_sub]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.GaussLine.pairInf_apply, Psi, EvAt0.PolD.arc, dotProduct, map_sum, map_mul, evIHom_apply]

theorem exists_pos_complex_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  choose R hRat hRmap using fun u : Matrix (Fin n) (Fin d) (AE F E) =>
    exists_mat_at hcm B.emb (fun w => Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ))
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, map_smul_piInf, hRmap]
    simp only [ Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _), hRmap]
    have hV := (hP.herm.cartan w).1
    have hW := (hP.skew.cartan w).1
    have hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]

  have hXh : ∀ w, ∀ i j, star (X.J.map (B.emb w).1 j i) = X.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.herm.herm]
  have hWs : ∀ w, ∀ i j, star (W.J.map (B.emb w).1 j i) = -W.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.skew.skew, map_neg]
  have hloc := fun w => _root_.GlobalTheory.CartanTensor.tensor_cartan_invariant_pos n d (X.J.map (B.emb w).1) (X.θ w) (W.J.map (B.emb w).1) (W.θ w) (hXh w)
    (hP.herm.cartan w) (hWs w) (hP.skew.cartan w)
  have key : ∀ a b : Matrix (Fin n) (Fin d) (AE F E),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) a b)) =
        ∑ w, -2 * (tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
          (b.map (piInf (B.emb w)))).re := by
    intro a b
    have ht := GlobalTheory.ThK.EvAt0.PlaneQ.trace_symp_neg_one F E σ hcm B.emb n d X.J W.J a b
    simp only [cA, incM] at ht
    rw [ht]
    rfl
  have hinv : ∀ a b w, tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((R a).map (piInf (B.emb w)))
      ((R b).map (piInf (B.emb w))) = tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
      (b.map (piInf (B.emb w))) := by
    intro a b w
    rw [hRmap, hRmap]
    exact (hloc w _ _).1
  have hpos : ∀ a w, a.map (piInf (B.emb w)) ≠ 0 → 0 < -(tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      (a.map (piInf (B.emb w))) ((R a).map (piInf (B.emb w)))).re := by
    intro a w ha
    rw [hRmap]
    exact (hloc w _ (a.map (piInf (B.emb w)))).2 ha
  let J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi M (R (Phi M w))
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v := by
    intro t v hv
    rw [← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  have hPsi0 : Psi M (0 : Matrix (Fin n) (Fin d) (AE F E)) = 0 := by
    have h := Psi_add M (0 : Matrix (Fin n) (Fin d) (AE F E)) 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  refine ⟨J₀, fun w => ?_, fun w w' => ?_, fun w hw => ?_, fun u u' hu hu' hmap => ?_⟩
  · show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w
    rw [Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]
  · show GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 (Psi M (R (Phi M w'))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w'))).1 (Psi M (R (Phi M w))).2 = _
    conv_rhs => rw [← Psi_Phi M w, ← Psi_Phi M w']
    rw [pair_Psi, pair_Psi, key, key]
    exact Finset.sum_congr rfl fun v _ => by rw [hinv]
  · have hw' := Psi_Phi M w
    have hat := at_Phi M w
    show 0 < GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) w.1 (Psi M (R (Phi M w))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 w.2
    generalize Phi M w = a at hw' hat ⊢
    subst hw'
    rw [pair_Psi, key]
    have hex : ∃ v, a.map (piInf (B.emb v)) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have ha0 : a = 0 := eq_of_map_piInf hcm B.emb hat (fun c _ => smul_zero c)
        fun v => by rw [hn v, Matrix.map_zero _ (map_zero _)]
      exact hw (by rw [ha0, hPsi0])
    obtain ⟨v, hv⟩ := hex
    refine Finset.sum_pos' (fun v' _ => ?_) ⟨v, Finset.mem_univ _, by have := hpos a v hv; linarith⟩
    by_cases h0 : a.map (piInf (B.emb v')) = 0
    · rw [h0, tensC_zero_left, Complex.zero_re, mul_zero]
    · have := hpos a v' h0; linarith
  · change Psi M u' = Psi M (R (Phi M (Psi M u)))
    rw [Phi_Psi M hu]
    congr 1
    exact eq_of_map_piInf hcm B.emb hu' (hRat u) fun w => by rw [hmap, hRmap]

end GlobalTheory.GaussFockPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTate

theorem torsion_card (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) {K : Type} [Field K]
    [IsSepClosed K] (t : Sp K ⟶ Sp ℂ) (z : Sp K) :
    Finite {x : Over.mk t ⟶ A // x ^ n = 1} ∧
      Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} = (torsion A n).hom.finrank (t z) := by
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := GlobalTheory.SepClosedTorsion.isUnit_natCast_top (by exact_mod_cast hn.ne')
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hu
  let e2 : (Over.mk t ⟶ torsion A n) ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    { toFun := fun y => ⟨y.left, Over.w y⟩
      invFun := fun x => Over.homMk x.1 x.2
      left_inv := fun y => Over.OverMorphism.ext rfl
      right_inv := fun x => rfl }
  let e : {x : Over.mk t ⟶ A // x ^ n = 1} ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    (GlobalTheory.TorsionUnram.torsionEquiv A n (Over.mk t)).symm.trans e2
  obtain ⟨h1, h2⟩ := GlobalTheory.FinEt.card_points_eq_finrank (torsion A n).hom t z
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans h2⟩

def toC {k : Type} [Field k] (j : ℂ →+* k) : Over.mk (spMap j) ⟶ Over.mk (𝟙 (Sp ℂ)) :=
  Over.homMk (spMap j) (Category.comp_id _)

theorem toC_left {k : Type} [Field k] (j : ℂ →+* k) : (toC j).left = spMap j := rfl

theorem pre_injective {k : Type} [Field k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A] :
    Function.Injective (preHom (G := A) (toC j)) := by
  intro x y h
  have hf : Flat (spMap j) := by
    rw [Flat.SpecMap_iff]
    letI := j.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap j) := ⟨fun q => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [preHom, MonoidHom.mk'_apply, Over.comp_left, toC_left] at h'
  exact (cancel_epi (spMap j)).1 h'

theorem pre_onto {k : Type} [Field k] [IsAlgClosed k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A]
    (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap j) ⟶ A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (𝟙 (Sp ℂ)) ⟶ A, y ^ n = 1 ∧ preHom (toC j) y = x := by
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨f₁, c₁⟩ := torsion_card A hA hn (spMap j) z
  obtain ⟨f₀, c₀⟩ := torsion_card A hA hn (𝟙 (Sp ℂ)) (spMap j z)
  let F : {x : Over.mk (𝟙 (Sp ℂ)) ⟶ A // x ^ n = 1} → {x : Over.mk (spMap j) ⟶ A // x ^ n = 1} :=
    fun y => ⟨preHom (toC j) y.1, by rw [← map_pow, y.2, map_one]⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective j A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁]; rfl)).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (j : ℂ →+* k) (c : ℂˣ) :
    Units.map (toC j).left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) := by
  rw [toC_left]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem one_comp_hom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] :
    (1 : T ⟶ G) ≫ φ = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

end GlobalTheory.HTTate

namespace GlobalTheory.UPel.HT


open Classical in
theorem exists_tateIsoO_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  intro p _ D N ρ A _ _ act L D' t Q e eta hN hNp hA hL hG hP hadd hsurj hker hact hW heta k _ _ x
  obtain ⟨f, ν, rfl, htow, hgen⟩ := hG
  obtain ⟨j, rfl⟩ : ∃ j : ℂ →+* k, spMap j = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hGF : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let π := preHom (G := A) (GlobalTheory.HTTate.toC j)
  have hπ : Function.Injective π := GlobalTheory.HTTate.pre_injective j A
  let e' : Multiplicative (Fin D.g → ℂ) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • Q (a + n • c)) = e ((n : ℂ)⁻¹ • Q a) := by
    intro n hn a c
    rw [map_add (f := _), smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  let ev : ℕ → D.La → (Over.mk (spMap j) ⟶ A) := fun n a =>
    if 0 < n ∧ n.Coprime p then π (e ((n : ℂ)⁻¹ • Q (f n a))) else 1
  have hev : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = π (e ((n : ℂ)⁻¹ • Q (f n a))) :=
    fun n hn hc a => if_pos ⟨hn, hc⟩
  have hev' : ∀ n, ¬ (0 < n ∧ n.Coprime p) → ∀ a, ev n a = 1 := fun n h a => if_neg h
  refine ⟨{ ζ := fun n => Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n))
            ζ_prim := fun n hn hc => (GlobalTheory.PeriodTate.rt_prim hn (hgen n hn hc).1).map_of_injective
              (Units.map_injective j.injective)
            ζ_pow := fun n m hn hm hc => by
              rw [← map_pow, GlobalTheory.PeriodTate.rt_pow hm, GlobalTheory.PeriodTate.rt_congr hn (htow n m hn hm hc).1]
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn hc a => ?_
            onto := fun n hn hc q => ?_
            tower := fun n m hn hm hc a => ?_
            isom := fun n hn hc a b => ?_ }, fun y => ?_⟩
  · by_cases h : 0 < n ∧ n.Coprime p
    · have hf : f n (a + b) = f n a + f n b := (f n).map_add a b
      rw [hev n h.1 h.2, hev n h.1 h.2, hev n h.1 h.2, hf, map_add (f := _), smul_add, hadd, map_mul]
    · rw [hev' n h, hev' n h, hev' n h, _root_.mul_one]
  · by_cases h : 0 < n ∧ n.Coprime p
    · rw [hev n h.1 h.2, hev n h.1 h.2]
      obtain ⟨d, hd⟩ := (hgen n h.1 h.2).2.1 c a
      replace hd : f n (c • a) = c • f n a + n • d := hd
      show π _ = π _ ≫ _
      rw [hd, hshift n h.1, show π (e ((n : ℂ)⁻¹ • Q (f n a))) ≫ act.act c =
        π (e ((n : ℂ)⁻¹ • Q (f n a)) ≫ act.act c) from Category.assoc _ _ _, ← hact, hP.1, Matrix.mulVec_smul]
    · rw [hev' n h, hev' n h]
      haveI := act.hom c
      exact (GlobalTheory.HTTate.one_comp_hom (act.act c)).symm
  · rw [hev n hn hc, map_eq_one_iff π hπ, hker]
    have hk : (∃ e, f n a = n • e) ↔ ∃ e : D.La, a = n • e := (hgen n hn hc).2.2.1 a
    rw [← hk]
    constructor
    · rintro ⟨c, hc'⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc', hsm n hn])⟩
    · rintro ⟨c, hc'⟩
      exact ⟨c, by rw [hc', map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := GlobalTheory.HTTate.pre_onto j A hA hn q hq
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hgen n hn hc).2.2.2.1 a'
      refine ⟨a, (hev n hn hc a).trans (congrArg π ?_)⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [hev n hn hc, ← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_right n m) hc
    obtain ⟨c, hc'⟩ := (htow n m hn hm hc).2 a
    replace hc' : f (n * m) a = f n a + n • c := hc'
    rw [hev _ (Nat.mul_pos hn hm) hc, hev n hn hn', ← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul,
      hsm m hm, hc', hshift n hn]
  · show Out.WeilIs A L n (ev n a) (ev n b)
      (unitOn (Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n)) ^ (2 * D.EF a b)))
    have h := GlobalTheory.CommPairing.weilIs_pull hGF hA hL (GlobalTheory.HTTate.toC j)
      (hW n (f n a) (f n b) (GlobalTheory.PeriodTate.rt n _) hn (GlobalTheory.PeriodTate.rt_val _ _))
    have e2 : D.plat.EF a b = 2 * D.EF a b := by
      show ((2 : ℤ) • D.EF) a b = _
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    have hν : (n : ℤ) ∣ D'.EF (f n a) (f n b) - ν n * (2 * D.EF a b) := by
      rw [← e2]; exact (hgen n hn hc).2.2.2.2 a b
    rw [GlobalTheory.HTTate.unitOn_pull, GlobalTheory.PeriodTate.rt_congr hn hν, GlobalTheory.PeriodTate.rt_mul, map_zpow] at h
    rw [hev n hn hc, hev n hn hc]
    exact h
  · show toUnit _ ≫ eta y = ev N y
    rw [hev N hN hNp]
    show _ = GlobalTheory.HTTate.toC j ≫ e _
    rw [← heta, ← Category.assoc]
    congr 1
end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalProjectionSectionIsotropicSpan
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory

theorem rational_proj_section_of_span : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ P Q : Matrix κ κ F,
      (∀ s ∈ S, (P.map (algebraMap F (AF F))) *ᵥ s.1 = 0) ∧
      (∀ s ∈ S, (s.1, (Q.map (algebraMap F (AF F))) *ᵥ s.1) ∈ S) ∧
      (∀ ξ : κ → F, P *ᵥ ξ = 0 →
        ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((Q *ᵥ ξ) i))) ∈ S) := by
  intro F _ _ κ _ S hS
  classical
  let ι := algebraMap F (AF F)
  let Φ : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    LinearMap.prodMap ((Algebra.linearMap F (AF F)).compLeft κ) ((Algebra.linearMap F (AF F)).compLeft κ)
  let T : Submodule F ((κ → F) × (κ → F)) := (S.restrictScalars F).comap Φ
  have hT : ∀ y z, (y, z) ∈ T ↔ ((fun i => ι (y i)), (fun i => ι (z i))) ∈ S := fun y z => Iff.rfl
  let f : T →ₗ[F] (κ → F) := LinearMap.fst F _ _ ∘ₗ T.subtype
  let L₁ := LinearMap.range f
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl L₁
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  let π : (κ → F) →ₗ[F] (κ → F) := C.subtype ∘ₗ Submodule.linearProjOfIsCompl C L₁ hC.symm
  let q : (κ → F) →ₗ[F] (κ → F) := LinearMap.snd F _ _ ∘ₗ T.subtype ∘ₗ g ∘ₗ Submodule.linearProjOfIsCompl L₁ C hC
  have hπ : ∀ y, π y = 0 ↔ y ∈ L₁ := by
    intro y
    simp only [π, LinearMap.comp_apply, Submodule.coe_subtype, ZeroMemClass.coe_eq_zero]
    exact Submodule.linearProjOfIsCompl_apply_eq_zero_iff hC.symm
  have hq : ∀ y ∈ L₁, (y, q y) ∈ T := by
    intro y hy
    have h1 : Submodule.linearProjOfIsCompl L₁ C hC y = ⟨y, hy⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨y, hy⟩
    have h2 : f.rangeRestrict (g ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hg ⟨y, hy⟩
    have h3 : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)).1 = y := by
      have := congrArg Subtype.val h2
      simpa [f] using this
    have hm := (g ⟨y, hy⟩).2
    have e : ((g ⟨y, hy⟩ : T) : (κ → F) × (κ → F)) = (y, q y) := by
      ext1
      · exact h3
      · simp [q, h1]
    rw [← e]; exact hm
  have hL : ∀ y z, (y, z) ∈ T → y ∈ L₁ := fun y z h => ⟨⟨(y, z), h⟩, rfl⟩
  have hmv : ∀ (M : Matrix κ κ F) (v : κ → F),
      (M.map ι) *ᵥ (fun i => ι (v i)) = fun i => ι ((M *ᵥ v) i) := by
    intro M v; funext i
    exact (RingHom.map_mulVec ι M v i).symm
  refine ⟨LinearMap.toMatrix' π, LinearMap.toMatrix' q, ?_, ?_, ?_⟩
  · intro s hs
    let A : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] (κ → AF F) :=
      (Matrix.mulVecLin ((LinearMap.toMatrix' π).map ι)) ∘ₗ LinearMap.fst _ _ _
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ LinearMap.ker A := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      have h0 : π y = 0 := (hπ y).2 hy
      show (LinearMap.toMatrix' π).map ι *ᵥ (fun i => ι (y i)) = 0
      rw [hmv, LinearMap.toMatrix'_mulVec, h0]
      funext i; simp
    exact hle (hS hs)
  · intro s hs
    let B : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F)) :=
      LinearMap.prod (LinearMap.fst _ _ _)
        ((Matrix.mulVecLin ((LinearMap.toMatrix' q).map ι)) ∘ₗ LinearMap.fst _ _ _)
    have hle : Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
        s = (fun i => ι (y i), fun i => ι (z i))} ≤ S.comap B := by
      rw [Submodule.span_le]
      rintro _ ⟨hs', y, z, rfl⟩
      have hy : y ∈ L₁ := hL y z hs'
      show ((fun i => ι (y i)), (LinearMap.toMatrix' q).map ι *ᵥ (fun i => ι (y i))) ∈ S
      rw [hmv, LinearMap.toMatrix'_mulVec]
      exact hq y hy
    exact hle (hS hs)
  · intro ξ hξ
    rw [LinearMap.toMatrix'_mulVec] at hξ
    have hx : ξ ∈ L₁ := (hπ ξ).1 hξ
    rw [LinearMap.toMatrix'_mulVec]
    exact hq ξ hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspForm_operator_act : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (o : Op E a) (φ : Sm E a), IsCuspForm φ → IsCuspForm (act o φ) := by
  first | exact @GlobalTheory.CuspStabFin.isCuspForm_act | exact GlobalTheory.CuspStabFin.isCuspForm_act | (intros; apply GlobalTheory.CuspStabFin.isCuspForm_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSetOfChartsMemStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_setOf_fibre_charts_mem : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (g₀ g₁ : Sp (Polynomial R) ⟶ Y), spMap (algebraMap (Polynomial R) (Localization.Away (Polynomial.X : Polynomial R))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) : Localization.Away (Polynomial.X : Polynomial R))).toRingHom ≫ g₁ → ∀ (W : Y.Opens), IsOpen {τ : Sp R | ∀ x : Sp (Polynomial R), spMap (algebraMap R (Polynomial R)) x = τ → g₀ x ∈ W ∧ g₁ x ∈ W} := by
  first | exact @GlobalTheory.isOpen_setOf_charts_mem | exact GlobalTheory.isOpen_setOf_charts_mem | (intros; apply GlobalTheory.isOpen_setOf_charts_mem <;> assumption)
end

