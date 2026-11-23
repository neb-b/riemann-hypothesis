module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulIntersectionNumberLeSectionDim
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem choose_mul_interNum_le_hdim : ∀ (k : Type) [Field k] [Infinite k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (N : ℕ) (b : Fin N → L.Sec), (∀ y : Y, ∃ i, y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i)) → ∀ (d : ℕ) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ d → ∀ (j₀ : ℤ), VanishFrom L F j₀ → ∀ m : ℕ, (m.choose d : ℤ) * GlobalTheory.interNum k F (fun _ : Fin d => L) ≤ GlobalTheory.hdim k (GlobalTheory.twistZ F L (j₀ + m)) 0 := by
  intro k _ _ Y _ hY L hL N b hb d
  have hNo : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hY
  have hb' : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (b i) = ⊤ :=
    top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hb y)
  have hf := algebraMap_eq_strHom k Y
  induction d with
  | zero =>
    intro F _ hF j₀ _ m
    rw [interNum_of_isEmpty, GlobalTheory.T.zero_dim_support_euler_char k Y hY L hL F (by simpa using hF)]
    simp
  | succ d ih =>
    intro F _ hF j₀ hV m
    obtain ⟨c, hc⟩ := exists_sum_mono_cutHom (k := k) F hL b hb'
    set t : L.Sec := ∑ i, algebraMap k Γ(Y, ⊤) (c i) • b i
    obtain ⟨hV', hr⟩ := GlobalTheory.T.hyperplane_section_vanishing_shift k Y hY L hL F t j₀ hV
    have hI : GlobalTheory.interNum k F (fun _ : Fin (d + 1) => L) =
        GlobalTheory.interNum k (GlobalTheory.cut F hL t) (fun _ : Fin d => L) := by
      rw [← interNum_cons_eq_interNum_cut hL t (P := fun _ : Fin d => L) (fun _ => hL)
        (finiteCohTwists_of_isProjOver hf F hY)]
      congr 1
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    have ih' := ih (GlobalTheory.cut F hL t) (suppDim_cut_le F hL t hF) (j₀ + 1) hV'
    rw [hI]
    induction m with
    | zero => simp
    | succ m ihm =>
      have h1 := hr (j₀ + 1 + m) (by omega)
      have h2 := ih' m
      have e1 : j₀ + ((m + 1 : ℕ) : ℤ) = j₀ + 1 + m := by push_cast; ring
      have e2 : j₀ + 1 + (m : ℤ) - 1 = j₀ + m := by ring
      rw [e2] at h1
      rw [e1, h1, Nat.choose_succ_succ']
      push_cast
      linarith

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZero
section
set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.HSChoice

namespace GlobalTheory.ChowZeroExt

def incIdeal {F : Type} [Field F] (B : ℕ) {N : ℕ} (I : Ideal (MvPolynomial (Fin N) F)) :
    Ideal (MvPolynomial ((Fin B × Fin N) ⊕ (Fin N ⊕ Fin N)) F) :=
  Ideal.span ((rename (fun j => Sum.inr (Sum.inl j)) '' (I : Set (MvPolynomial (Fin N) F))) ∪
    (Set.range (fun i : Fin B => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr (Sum.inl j))) ∪
      {∑ j, X (Sum.inr (Sum.inr j)) * X (Sum.inr (Sum.inl j)) - 1}))

theorem forall_span_iff {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] (S : Set (MvPolynomial ι F))
    (x : ι → Ω) : (∀ g ∈ Ideal.span S, aeval x g = 0) ↔ ∀ g ∈ S, aeval x g = 0 := by
  refine ⟨fun h g hg => h g (Ideal.subset_span hg), fun h g hg => ?_⟩
  have : Ideal.span S ≤ RingHom.ker (aeval x : MvPolynomial ι F →ₐ[F] Ω) :=
    Ideal.span_le.2 fun g hg => h g hg
  exact this hg

theorem forall_incIdeal_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {B N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) F)) (x : (Fin B × Fin N) ⊕ (Fin N ⊕ Fin N) → Ω) :
    (∀ g ∈ incIdeal B I, aeval x g = 0) ↔
      (∀ g ∈ I, aeval (fun j => x (Sum.inr (Sum.inl j))) g = 0) ∧
      (∀ i, ∑ j, x (Sum.inl (i, j)) * x (Sum.inr (Sum.inl j)) = 0) ∧
      ∑ j, x (Sum.inr (Sum.inr j)) * x (Sum.inr (Sum.inl j)) = 1 := by
  rw [incIdeal, forall_span_iff]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun i => ?_, ?_⟩
    · have := h _ (Or.inl ⟨g, hg, rfl⟩)
      rwa [aeval_rename] at this
    · simpa using h _ (Or.inr (Or.inl ⟨i, rfl⟩))
    · simpa [sub_eq_zero] using h _ (Or.inr (Or.inr rfl))
  · rintro ⟨h1, h2, h3⟩ g (⟨g, hg, rfl⟩ | ⟨i, rfl⟩ | rfl)
    · rw [aeval_rename]
      exact h1 g hg
    · simpa using h2 i
    · simpa [sub_eq_zero] using h3

theorem exists_dual {Ω : Type} [Field Ω] {N : ℕ} {y : Fin N → Ω} (hy : y ≠ 0) :
    ∃ z : Fin N → Ω, ∑ j, z j * y j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  refine ⟨Pi.single j (y j)⁻¹, ?_⟩
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
    exact inv_mul_cancel₀ hj
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem ne_zero_of_dual {Ω : Type} [Field Ω] {N : ℕ} {y z : Fin N → Ω} (h : ∑ j, z j * y j = 1) :
    y ≠ 0 := by
  rintro rfl
  simp at h

variable {F : Type} [Field F] {D N d : ℕ} {I : Ideal (MvPolynomial (Fin N) F)}
  {f : MvPolynomial (Fin (D + 1) × Fin N) F}

theorem aeval_eq_zero_of_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω]
    (u : Fin (D + 1) × Fin N → Ω) (y : Fin N → Ω) (hy : y ≠ 0) (hI : ∀ g ∈ I, aeval y g = 0)
    (hu : ∀ i, ∑ j, u (i, j) * y j = 0) : aeval u f = 0 := by
  obtain ⟨z, hz⟩ := exists_dual hy
  have key := _root_.GlobalTheory.vanish_transfer_of_algClosure F _ (incIdeal (D + 1) I) (rename Sum.inl f) (fun x hx => by
    obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I x).1 hx
    rw [aeval_rename]
    exact (hf.zero_iff _).2 ⟨_, ne_zero_of_dual h3, h1, h2⟩) Ω (Sum.elim u (Sum.elim y z))
    ((forall_incIdeal_iff I _).2 ⟨hI, hu, hz⟩)
  rwa [aeval_rename] at key

theorem exists_common_zero (hf : IsChowForm I D d f) {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    (u : Fin (D + 1) × Fin N → Ω) (hu : aeval u f = 0) :
    ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ ∀ i, ∑ j, u (i, j) * y j = 0 := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.polynomial_solvability_transfer_algClosed_fields F _ _ (Ideal.span {f}) (incIdeal (D + 1) I) (fun v hv => by
    obtain ⟨y, hy, h1, h2⟩ := (hf.zero_iff v).1 (hv f (Ideal.subset_span rfl))
    obtain ⟨z, hz⟩ := exists_dual hy
    exact ⟨Sum.elim y z, (forall_incIdeal_iff I _).2 ⟨h1, h2, hz⟩⟩) Ω u
    ((forall_span_iff _ _).2 (by rintro g rfl; exact hu))
  obtain ⟨h1, h2, h3⟩ := (forall_incIdeal_iff I _).1 hw
  exact ⟨_, ne_zero_of_dual h3, h1, h2⟩

theorem forall_join_iff {Ω : Type} [Field Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω) :
    (∀ i, ∑ j, join s ξ (i, j) * y j = 0) ↔ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0 := by
  rw [Fin.forall_fin_succ']
  simp [join]

theorem zero_set_ext : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F))
    (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f →
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 →
      (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 →
      aeval (join s ξ) f = 0) ∧
    (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω),
      aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧
        (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  intro F _ _ D N d I f hf
  refine ⟨fun Ω _ _ s ξ y hy hI hs hξ => ?_, fun Ω _ _ _ s ξ h => ?_⟩
  · exact aeval_eq_zero_of_common_zero hf _ y hy hI ((forall_join_iff s ξ y).2 ⟨hs, hξ⟩)
  · obtain ⟨y, hy, h1, h2⟩ := exists_common_zero hf _ h
    exact ⟨y, hy, h1, (forall_join_iff s ξ y).1 h2⟩

end GlobalTheory.ChowZeroExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CsdTwistGal

theorem infChar_conj_of_isCsd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (P : CuspSub E a), P.IsCsd →
    ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), P.HasInfChar τ m →
      P.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  intro E _ _ _ a P hP τ m m' hm hm'
  have h1 : (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
    obtain ⟨T, hT⟩ := hP
    refine ⟨((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨φ, rfl⟩ := ((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).surjective φ
    have e : (GlobalTheory.ThetaPull.thetaSub P).op o ((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V φ) =
        (GlobalTheory.ThetaPull.pull E a).submoduleMap P.V (P.op (thetaOp o) φ) :=
      Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
    rw [e]
    exact (congrArg T (((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply _)).trans
      ((hT o φ).trans (congrArg (P.op o)
        (congrArg T (((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply φ)).symm))
  have h2 : (GlobalTheory.ThetaPull.thetaSub P).HasInfChar τ (m'.map Neg.neg) := by
    refine ⟨by rw [Multiset.card_map, hm'.1], ?_⟩
    rintro u _ ⟨φ, hφ, rfl⟩
    change cap τ u (GlobalTheory.ThetaPull.pull E a φ) = _ • GlobalTheory.ThetaPull.pull E a φ
    rw [GlobalTheory.ThetaPull.cap_pull, LinearMap.smul_apply, hm'.2 _ φ hφ, smul_smul, map_smul]
    congr 1
    have e : ((m'.map Neg.neg).map (u + ·)) = (m'.map (-u + ·)).map Neg.neg := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]; ring
    rw [e, Multiset.prod_map_neg, Multiset.card_map, hm'.1]
  have h4 := (h1.hasInfChar h2).unique hm
  rw [← h4, Multiset.map_map]
  simp

theorem rec_twist_absPow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
    (rc : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ),
      rc (GlobalTheory.LocGL.IrrGL.of (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
        (CuspSub.isOpen_ker_locDet _ w)).ρ (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
        (CuspSub.isOpen_ker_locDet _ w)).smooth (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
        (CuspSub.isOpen_ker_locDet _ w)).irred) = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw s := by
  intro E Ω _ _ _ _ _ _ w B h rc hrc a σ s
  obtain ⟨_, _, _, -, H⟩ := hrc
  rw [← H.nu_eq]
  refine congrArg _ ((GlobalTheory.LocGL.IrrGL.tw_of σ.ρ σ.smooth σ.irred _
    (GlobalTheory.CuspRep.ParLaws.isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E s) w)).symm.trans ?_)
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s) w

theorem exists_galRep_csd_twist : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a))) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  intro hG _ _ _ _ hLL E Ω _ _ _ _ _ _ _ l _ ι a ha P hP m hm hnd f J hJ
  have hτ : ∀ σ : E →+* ℂ, ι.toRingHom.comp (ι.symm.toRingHom.comp σ) = σ := fun σ => by
    ext x; simp
  have hint : ∀ σ : E →+* ℂ, ∀ z ∈ m σ, ∃ k : ℤ, f - z = k := by
    intro σ z hz
    have h1 := hJ (ι.symm.toRingHom.comp σ)
    rw [hτ] at h1
    have h2 : f - z ∈ (m σ).map (fun z => f - z) := Multiset.mem_map_of_mem _ hz
    rw [← h1] at h2
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 h2
    exact ⟨k, hk.symm⟩
  have hfre : f = ((f.re : ℝ) : ℂ) := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨z, hz⟩ : ∃ z, z ∈ m τ0 := Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ0).1]; omega)
    have hc := infChar_conj_of_isCsd E a P hP τ0 _ _ (hm τ0) (hm _)
    have hz' : -z ∈ m (NumberField.ComplexEmbedding.conjugate τ0) := by
      rw [hc]; exact Multiset.mem_map_of_mem _ hz
    obtain ⟨k1, hk1⟩ := hint _ z hz
    obtain ⟨k2, hk2⟩ := hint _ _ hz'
    have e1 := congrArg Complex.im hk1
    have e2 := congrArg Complex.im hk2
    simp only [Complex.sub_im, Complex.intCast_im, Complex.neg_im] at e1 e2
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]; linarith
  set s : ℝ := ((a : ℝ) - 1) / 2 - f.re with hs
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hexpo : ∀ τ, expo (GlobalTheory.HeckeGal.Model.absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s hν
  have hm' : ∀ τ, (P.twist (GlobalTheory.HeckeGal.Model.absPow E s)).HasInfChar τ ((m τ).map (· + (s : ℂ))) := fun τ => by
    have := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rwa [hexpo] at this
  have hinf' : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) :=
    fun τ => CG.HasInfChar.infChar_eq (hm' τ)
  have hr : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf' τ]
    refine ⟨(hnd τ).map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨k, hk⟩ := hint τ y hy
    refine ⟨-k, ?_⟩
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hk + hfre
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι a ha _ _ hr (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s)
  have hHT : ∀ τ, HT τ = J τ := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hinf', hJ τ, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    rw [hs]; push_cast
    linear_combination (-1 : ℂ) * hfre
  refine ⟨r, H.cont, fun hsph => ⟨H.cont, fun PP AI T w A h O _ _ _ Bw hj => ?_⟩, ?_⟩
  · have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := hj.mem_placesOver h
    obtain ⟨σ, hσ, hsp⟩ := hsph w hw
    have HA := H.above PP AI T w A h O Bw hj
    refine ⟨HA.crys _ (hσ.twist _) (GlobalTheory.T.isSpherical_twist_absDetPow_GL E a w σ s hsp), fun τ LL' τ' hτ' => ?_⟩
    rw [← hHT]
    exact HA.jumps τ LL' τ' hτ'
  · intro w _ hl σ hσ S hS B g hB hg
    obtain ⟨rc, hrc⟩ := (hLL.1 E Ω B w hB).exists
    have e1 := H.wdOf_eq hl hrc (hσ.twist (GlobalTheory.HeckeGal.Model.absPow E s))
    rw [rec_twist_absPow E Ω w B hB rc hrc a σ s, GlobalTheory.WeilDeligne.WD.lpTw_add] at e1
    rw [GlobalTheory.T.local_langlands_galois_compat E Ω l ι a r H.cont w hl B hB rc hrc σ S hS _ e1 g hg]
    have e2 : ((-(s + (1 - (a : ℝ)) / 2) : ℝ) : ℂ) = f := by
      rw [hfre, hs]; push_cast; ring
    rw [e2]

end GlobalTheory.CsdTwistGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffLinearSubstColumnMemIntegralLattice
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.CoeffInt

theorem word_col {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (g : Fin t → Fin n) :
    word mul (fun i => w.col (g i)) =
      ∑ e : Fin t → Fin N, (∏ i, w (e i) (g i)) • word mul (fun i => Pi.single (e i) 1) := by
  let Φ := (MultilinearMap.mkPiAlgebraFin K t (Module.End K A)).compLinearMap (fun _ => mul)
  have hΦ : ∀ u : Fin t → Fin N → K, word mul u = Φ u := by
    intro u; simp [Φ, word, MultilinearMap.mkPiAlgebraFin_apply]
  have hcol : ∀ i, w.col (g i) = ∑ j, w j (g i) • (Pi.single j 1 : Fin N → K) := by
    intro i; funext k; simp [Matrix.col, Finset.sum_apply, Pi.single_apply]
  rw [hΦ]
  simp_rw [hcol]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MultilinearMap.map_smul_univ, hΦ]
  rfl

theorem linSubst_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N n B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (w : Matrix (Fin N) (Fin n) K) (c : A →ₗ[K] K)
    (β : Fin t → Fin B) (x : A) :
    linSubst w (coordP mul c β x) =
      ∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K) := by
  rw [show (∑ g : Fin t → Fin n, C (c (word mul (fun i => w.col (g i)) x)) *
        ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) =
      ∑ g : Fin t → Fin n, ∑ e : Fin t → Fin N, C (c (word mul (fun i => Pi.single (e i) 1) x)) *
        ((∏ i, C (w (e i) (g i))) * ∏ i, (X (β i, g i) : MvPolynomial (Fin B × Fin n) K)) from ?_]
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [linSubst, coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, algebraMap_eq]
    simp_rw [Fintype.prod_sum, Finset.mul_sum, ← Finset.prod_mul_distrib]
    exact Finset.sum_comm
  · refine Finset.sum_congr rfl fun g _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [word_col, LinearMap.sum_apply, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, ← map_prod, map_mul]
    ring

theorem prod_X_monomial {σ K : Type} [Field K] {t : ℕ} (f : Fin t → σ) :
    ∃ s, (∏ i, (X (f i) : MvPolynomial σ K)) = monomial s 1 := by
  refine Finset.prod_induction _ (fun q => ∃ s, q = monomial s 1) ?_ ?_ ?_
  · rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩; exact ⟨s + s', by rw [monomial_mul, one_mul]⟩
  · exact ⟨0, by simp⟩
  · intro i _; exact ⟨_, rfl⟩

end GlobalTheory.HSShort.CoeffInt


open GlobalTheory.HSShort.CoeffInt in
theorem GlobalTheory.HSShort.colCoeff_mem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ κ : S.Col, κ.x ∈ S.M κ.j → ∀ m, ∑ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m • b i ∈ S.M S.T := by
  intro F A _ _ _ _ _ _ S hS d b c hco κ hx m
  obtain ⟨-, hM⟩ := _root_.GlobalTheory.HSShort.wordMem F A S hS κ.j κ.t (le_of_eq κ.add)
  have tr : ∀ j', j' = S.T → ∀ y' ∈ S.M j', ∃ y ∈ S.M S.T, (y : A) = (y' : A) := by
    rintro j' rfl y' hy'; exact ⟨y', hy', rfl⟩
  have key : ∀ g : Fin κ.t → Fin S.n, ∃ y ∈ S.M S.T,
      (y : A) = word S.mul (fun i => S.w.col (g i)) (κ.x : A) := by
    intro g
    obtain ⟨y, hy, hyeq⟩ := hM g κ.x hx
    obtain ⟨z, hz, hzeq⟩ := tr _ κ.add y hy
    exact ⟨z, hz, hzeq.trans hyeq⟩
  choose Y hY hYeq using key
  have hex : ∀ g : Fin κ.t → Fin S.n, ∃ s,
      (∏ i, (X (κ.β i, g i) : MvPolynomial (Fin _ × Fin S.n) F)) = monomial s 1 := by
    intro g
    exact GlobalTheory.HSShort.CoeffInt.prod_X_monomial (K := F) (fun i => (κ.β i, g i))
  choose s hs using hex
  have hcoef : ∀ i, AddMonoidAlgebra.coeff (linSubst S.w (coordP S.mul (c i) κ.β (κ.x : A))) m =
      ∑ g, b.repr (Y g) i * (if s g = m then 1 else 0) := by
    intro i
    rw [GlobalTheory.HSShort.CoeffInt.linSubst_coordP, coeff_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_C_mul, hs g, coeff_monomial, ← hYeq g, hco]
  simp_rw [hcoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Submodule.sum_mem _ fun g _ => ?_
  have hsum : ∑ i, (b.repr (Y g) i * (if s g = m then (1 : F) else 0)) • b i =
      (if s g = m then (1 : F) else 0) • Y g := by
    conv_rhs => rw [← b.sum_repr (Y g), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hsum]
  split_ifs
  · rw [one_smul]; exact hY g
  · rw [zero_smul]; exact zero_mem _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


theorem realAd_mul (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

end GlobalTheory.ThetaDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)),
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ W v, ∀ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.InertDbl.matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
      At (evFin F v) ((t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
        ((t⁻¹ : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertDbl.parD_diag_action | exact GlobalTheory.InertDbl.parD_diag_action | (intros; apply GlobalTheory.InertDbl.parD_diag_action <;> assumption)
end

