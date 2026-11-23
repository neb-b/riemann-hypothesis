module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem isOpenEmbedding_entriesGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_entriesGLInf.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem IsRapidFInf.integrable {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin n) (Cinf E)} {η : X → Z →L[ℝ] ℝ} (h : IsRapidFInf ν k γ η)
    {W : GL (Fin n) (Cinf E) → ℂ} (hW : IsModGrowthInf W) (z : Z) (g : GL (Fin n) (Cinf E)) :
    Integrable (fun x => k x * (𝐞 (η x z) : ℂ) * W (g * γ x)) ν := by
  obtain ⟨hc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  refine ((h.2.2.2 N).const_mul (C * htInf g ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Measurable.aestronglyMeasurable ((h.1.mul ?_).mul ?_)
    · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp (h.2.2.1 z)
    · exact measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop) h.2.1
  · rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    have h1 : htInf (g * γ x) ≤ htInf g * (htInf (γ x) * (1 + ‖η x‖)) :=
      (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (htInf_pos' _).le (by linarith [norm_nonneg (η x)])) (htInf_pos' _).le)
    have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
    rw [mul_pow] at h2
    calc ‖k x‖ * ‖W (g * γ x)‖ ≤ ‖k x‖ * (C * (htInf g ^ N * (htInf (γ x) * (1 + ‖η x‖)) ^ N)) :=
          mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = _ := by ring

theorem isKerOpInf_zero_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsKerOpInf (E := E) (n := n)
      (fun (_ : GL (Fin n) (Cinf E) → ℂ) (_ : Z) (_ : GL (Fin n) (Cinf E)) => (0 : ℂ)) := by
  refine ⟨Unit, inferInstance, 0, inferInstance, fun _ => 0, fun _ => 1, fun _ => 0, ?_, ?_⟩
  · exact ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_zero_measure⟩
  · intro W _ z g
    simp

theorem isKerOpInf_add_sum {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ} (hT : IsKerOpInf T) (hT' : IsKerOpInf T') :
    IsKerOpInf (fun W z g => T W z g + T' W z g) := by
  obtain ⟨X, mX, ν, hν, k, γ, η, hr, hT⟩ := hT
  obtain ⟨X', mX', ν', hν', k', γ', η', hr', hT'⟩ := hT'
  have e1 : MeasurableEmbedding (Sum.inl : X → X ⊕ X') :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => measurableSet_inl_image.2 hs⟩
  have e2 : MeasurableEmbedding (Sum.inr : X' → X ⊕ X') :=
    ⟨Sum.inr_injective, measurable_inr, fun _ hs => measurableSet_inr_image.2 hs⟩
  refine ⟨X ⊕ X', inferInstance, ν.map Sum.inl + ν'.map Sum.inr, inferInstance, Sum.elim k k', Sum.elim γ γ',
    Sum.elim η η', ?_, ?_⟩
  · refine ⟨hr.1.sumElim hr'.1, fun i j => ?_, fun z => ?_, fun N => ?_⟩
    · have : (fun x : X ⊕ X' => ((Sum.elim γ γ' x : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
          Sum.elim (fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j)
            (fun x => (γ' x : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.1 i j).sumElim (hr'.2.1 i j)
    · have : (fun x : X ⊕ X' => Sum.elim η η' x z) = Sum.elim (fun x => η x z) (fun x => η' x z) := by
        funext x; cases x <;> rfl
      rw [this]; exact (hr.2.2.1 z).sumElim (hr'.2.2.1 z)
    · rw [integrable_add_measure, e1.integrable_map_iff, e2.integrable_map_iff]
      exact ⟨hr.2.2.2 N, hr'.2.2.2 N⟩
  · intro W hW z g
    have i1 := hr.integrable hW z g
    have i2 := hr'.integrable hW z g
    show T W z g + T' W z g = _
    rw [integral_add_measure, e1.integral_map, e2.integral_map, hT W hW z g, hT' W hW z g]
    · rfl
    · rw [e1.integrable_map_iff]; exact i1
    · rw [e2.integrable_map_iff]; exact i2

theorem isKerOpInf_fintype_sum (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι]
    (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) (hT : ∀ i, IsKerOpInf (T i)) :
    IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  classical
  suffices h : ∀ s : Finset ι, IsKerOpInf (fun W z g => ∑ i ∈ s, T i W z g) from h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using (isKerOpInf_zero_sum (E := E) (n := n) (Z := Z))
  | insert a s ha ih =>
    have : (fun W z g => ∑ i ∈ insert a s, T i W z g) = fun W z g => T a W z g + ∑ i ∈ s, T i W z g := by
      funext W z g; rw [Finset.sum_insert ha]
    rw [this]
    exact isKerOpInf_add_sum (hT a) ih

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSpecialUnitarySupportedAtPlaces
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

namespace GlobalTheory.SUSuppClosed

theorem isClosed_SUSupp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) : IsClosed (SUSupp σ J ε) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hv : Continuous fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (AF F) σ J).continuous
  have h1 : IsClosed {g : HA (AF F) σ J | g ∈ SUAdelic σ J} := by
    simp only [StrongApprox.mem_SUAdelic]
    exact isClosed_eq hv.matrix_det continuous_const
  have h2 : IsClosed {g : HA (AF F) σ J | ∀ i j,
      algebraMap (AF F) (AF F ⊗[F] E) ε * (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j =
        (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun g : HA (AF F) σ J =>
        (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j :=
      (hv.sub continuous_const).matrix_elem i j
    exact isClosed_eq (continuous_const.mul hc) hc
  exact h1.inter h2

end GlobalTheory.SUSuppClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesBis
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (X : Set (AF F ⊗[F] E)) (hX : IsCompact X) (hcl : IsClosed (SUSupp σ J ε)) (hent : ∀ g ∈ SUSupp σ J ε, ∀ i j, ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j ∈ X) : IsCompact (SUSupp σ J ε) := by
  have hinv : ∀ g ∈ SUSupp σ J ε, g⁻¹ ∈ SUSupp σ J ε := by
    intro g hg
    rw [GlobalTheory.SUSuppSub.mem_SUSupp_iff] at hg ⊢
    exact ⟨(SUAdelic σ J).inv_mem hg.1, GlobalTheory.SUSuppSub.fix_inv _ (GlobalTheory.SUSuppSub.mv_inv_mul σ J g) hg.2⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let S : Set (Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => X
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hX
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  have hL := (GlobalTheory.AdelicU.isClosedEmbedding_matHom_GAd σ J).isCompact_preimage hK
  refine hL.of_isClosed_subset hcl fun g hg => ?_
  refine ⟨fun i _ j _ => hent g hg i j, ((HA.mat (AF F) σ J g⁻¹).1), fun i _ j _ => hent g⁻¹ (hinv g hg) i j, ?_⟩
  rfl
end GlobalTheory.SUSuppCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspIndProdCharOfIsProdCuspChar
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealOneVector

theorem isCuspIndProdChar_of_isProdCuspChar {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (s : K →+* ℂ)
    (Pg : Finset (Pl E)) (r : ℕ) (χ : G0 Pg r → K) (h : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar s Pg r χ) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  obtain ⟨θ, hθ, hχ⟩ := h
  refine ⟨θ, fun PP => ?_, hχ⟩
  obtain ⟨d, b, σ, hσ, hx⟩ := hθ PP
  exact ⟨b, Fin d → ℂ, inferInstance, inferInstance, inferInstance, σ, hσ, hx⟩

theorem typeSum_base_eq_card : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P0], ∀ χ ∈ A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hind _ χ hχ
  have h := GlobalTheory.OneForm.oneVector_of_whittaker R F GlobalTheory.GenericProduct.oneWhittakerVector_holds hlev
    (fun χ hχ => isCuspIndProdChar_of_isProdCuspChar _ _ _ _ (hind χ hχ)) χ hχ
  rw [← Nat.card_eq_fintype_card, ← h, GlobalTheory.OneForm.typeSum]
  congr 1
  exact congrArg (fun i => @Finset.univ _ i) (Subsingleton.elim _ _)

end GlobalTheory.RealOneVector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem pullbackGerm_finset_sum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {K : Type} (s : Finset K)
    (a : K → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem isMat_germ : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB R _ t A' B' _ _ φA' φB' Φ' c h
  obtain ⟨ψA, ψB, α, h1, h2, -, -, hch⟩ := h
  refine ⟨ψA, ψB, h1, h2, ?_⟩
  intro Z e z pM q hM hA
  have hz : e z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q) := by
    refine ⟨?_, ?_⟩
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hM i
      simpa using this
    · refine Set.mem_iInter.2 fun i => ?_
      have := Set.mem_iInter.1 hA i
      simpa using this
  refine ⟨gm e z _ (α.s (pM, q)), fun j => ?_⟩
  have E := congrArg (gs e z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U (pM, q))) (hch j (pM, q))
  erw [gs_mul _ _ _ hz] at E
  erw [gs_unit _ _ _ hz, pullbackGerm_finset_sum _ _ _ hz, gs_appLE _ _ _ _ _ _ hz] at E
  refine E.trans (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  erw [gs_mul _ _ _ hz, gs_appLE _ _ _ _ _ _ hz, gs_appLE _ _ _ _ _ _ hz]
  rfl

end GlobalTheory.HomFixMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevTrans

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frGL_conj {n : ℕ} (β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (u y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (β' * intGL F E n u * β⁻¹) * frGL β y * (β' * intGL F E n u * β⁻¹)⁻¹ = frGL β' (u * y * u⁻¹) := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

theorem transport {n n' : ℕ} (h : n = n') (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (β' x' : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (u : GL (Fin n') (Formalism.L2.Herm.intAf F E))
    (j : Matrix (Fin n') (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hc : HMul.hMul x'.val j = HMul.hMul j x.val)
    (hf : HMul.hMul j β.val = (β' * intGL F E n' u).val.submatrix id (Fin.cast h))
    (Pg : Finset (Pl E)) (hu : ∀ PP ∈ Pg, Formalism.UG.bc (resS F PP) u = 1) (r t : ℕ) (hr : r ≤ n) (hr' : r ≤ n') :
    (x ∈ St β ↔ x' ∈ St β') ∧ (x ∈ St β → ∀ PP ∈ Pg,
      (redFn β PP x ∈ blockTri (blkOf r t) ↔ redFn β' PP x' ∈ blockTri (blkOf r t)) ∧
        upperLeftBlock hr' (redFn β' PP x') = upperLeftBlock hr (redFn β PP x)) := by
  subst h
  have hf' : j * β.val = (β' * intGL F E n u).val := hf
  set J : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := β' * intGL F E n u * β⁻¹ with hJ
  have hj : j = J.val := by
    rw [hJ, Units.val_mul, ← hf', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hx : x' = J * x * J⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    show x'.val * J.val = J.val * x.val
    rw [← hj]
    exact hc
  have key : ∀ y, J * frGL β y * J⁻¹ = frGL β' (u * y * u⁻¹) := frGL_conj β β' u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨u * y * u⁻¹, by rw [hx, key]⟩
  · rintro ⟨y, hy⟩
    refine ⟨u⁻¹ * y * u, ?_⟩
    have h1 := key (u⁻¹ * y * u)
    rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group, hy, hx] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rintro ⟨y, rfl⟩ PP hP
    have h2 : redFn β' PP x' = redFn β PP (frGL β y) := by
      rw [hx, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, hu PP hP]
      simp
    rw [h2]
    exact ⟨Iff.rfl, rfl⟩

end General

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem finE_unitary (V : HSp D) (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have h2 := congrArg (fun M => Matrix.map M ((swapAE D).comp (finPart D))) h
  simp only [Matrix.map_mul] at h2
  show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _
  rw [show (finE V g).1 = (Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)) from rfl]
  have e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map ((swapAE D).comp (finPart D)) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D))) := by
    ext i j
    exact fin_cA _
  rw [e1] at h2
  exact h2

theorem levtrans : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  intro D V V' β β' r t hr hr' Pg χ χ' j Φ hI κ
  obtain ⟨h, u, hf, hu⟩ := hI.frame
  obtain ⟨h1, h2⟩ := transport h β (finE V (κ : GA D V)) β' (finE V' (Φ κ : GA D V')) u j (hI.conj κ) hf Pg hu r t hr hr'
  refine ⟨?_, fun hm => ?_⟩
  · rw [mem_parLev, mem_parLev]
    constructor
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.1 a, fun PP hP => ((h2 a PP hP).1).1 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.2 a, fun PP hP => ((h2 (h1.2 a) PP hP).1).2 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
  · funext PP
    exact (h2 (parLev_St hm) PP.1 PP.2).2

end GlobalTheory.LevTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpread
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegBundleSpread

theorem lbIso_spread : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ j₂ φ₂ hj hj₂ hej hφ₂ heφ
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ.w
  have hcomp : j₂ ≫ ψ₂ = φ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hj₂ hψ₂ hφ₂
  have hpb : IsPullback j₂ (G2 e.A).hom (G2 d₀.A).hom (spMap R₀.subtype) :=
    GlobalTheory.SiegDesc.isPullback_of_isSquare hj hj₂
  haveI : IsProper d₀.A.hom := d₀.ab.proper
  haveI : IsProper (G2 d₀.A).hom := by
    change IsProper (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom)
    infer_instance
  have hN : (u.P.pull ψ₂).IsLB := pull_isLB u.isLB ψ₂
  have H : LBIso (d₀.P.pull j₂) ((u.P.pull ψ₂).pull j₂) := by
    have a : LBIso (d₀.P.pull j₂) (u.P.pull φ₂) :=
      LBIso.trans (pull_isLB d₀.isLB _) e.isLB (pull_isLB u.isLB _) (LBIso.symm hej) heφ
    have b : LBIso (u.P.pull φ₂) ((u.P.pull ψ₂).pull j₂) := by
      rw [← hcomp]
      exact LBIso.symm (GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ j₂)
    exact LBIso.trans (pull_isLB d₀.isLB _) (pull_isLB u.isLB _) (pull_isLB hN _) a b
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ (G2 e.A).left (G2 d₀.A).left
    (G2 e.A).hom (G2 d₀.A).hom j₂ d₀.P (u.P.pull ψ₂) hpb d₀.isLB hN H
  refine ⟨F, fun R₁ hle hFR s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁ hφ₁₂ hd₁ hχ₂ => ?_⟩
  have hcomp₁ : φ₁₂ ≫ ψ₂ = χ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hφ₁₂ hψ₂ hχ₂
  have H₁ := hF R₁ hle hFR (G2 d₁.A).left (G2 d₁.A).hom φ₁₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ₁ hφ₁₂)
  have c : LBIso ((u.P.pull ψ₂).pull φ₁₂) (u.P.pull χ₂) := by
    rw [← hcomp₁]
    exact GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ φ₁₂
  exact LBIso.trans d₁.isLB (pull_isLB hN _) (pull_isLB u.isLB _)
    (LBIso.trans d₁.isLB (pull_isLB d₀.isLB _) (pull_isLB hN _) hd₁ H₁) c

end GlobalTheory.SiegBundleSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariant
section
noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem postOn_gaL {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (x : MMap M) :
    postOn M (gaL V β L eG c) x = ∑ g, c g • postOn M (actL V β L (eG g)) x := by
  ext v h
  simp [postOn, gaL, LinearMap.sum_apply, Finset.sum_apply]

variable {R} {F : Face D A}

end Record

end GlobalTheory.AdjBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewiseStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_iff_placewise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E, z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), Valued.v (z w - a w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  first | exact @GlobalTheory.CMVal.HatPlace.mem_hatO_iff | exact GlobalTheory.CMVal.HatPlace.mem_hatO_iff | (intros; apply GlobalTheory.CMVal.HatPlace.mem_hatO_iff <;> assumption)
end

