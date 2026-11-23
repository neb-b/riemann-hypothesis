module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.HeckeExtend

theorem exists_int_of_mem_intF : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ), 0 < m →
    algebraMap F (AF F) y ∈ intF F m → ∃ r : 𝓞 F, y = m * r := by
  intro F _ _ y m hm hy
  obtain ⟨c, hc, e⟩ := hy
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y / m) ≤ 1 := by
    intro v
    have h1 : (y : v.adicCompletion F) = ((m : F) : v.adicCompletion F) * c v := by
      have := congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) e
      simp only [nsmul_eq_mul] at this
      have hL : (algebraMap F (AF F) y).2 v = (y : v.adicCompletion F) := rfl
      have hm' : ((m : FiniteAdeleRing (𝓞 F) F)) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) :=
        (map_natCast _ m).symm
      have hR : ((m : FiniteAdeleRing (𝓞 F) F) * c) v = ((m : F) : v.adicCompletion F) * c v := by
        rw [hm']; rfl
      rw [← hL, ← hR]
      exact this
    have h2 : v.valuation F y = v.valuation F (m : F) * Valued.v (c v) := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h1, map_mul,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hv0 : v.valuation F (m : F) ≠ 0 := (Valuation.ne_zero_iff _).2 hmF
    rw [map_div₀, h2, mul_div_cancel_left₀ _ hv0]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (hc v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y / (m : F)) key
  refine ⟨r, ?_⟩
  have : ((r : 𝓞 F) : F) = y / m := hr
  rw [this, mul_div_cancel₀ _ hmF]

end GlobalTheory.HeckeExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvolutiveAlgebraAdjoinRootSelfReciprocal
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.InvAlgConstr

theorem exists_invAlg_adjoinRoot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (t : K.O), t ≠ 0 → ∀ Q : (w.adicCompletion E)[X], Q.Monic → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ ∧ aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧ (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 := by
  intro E _ _ _ w hw K e he t ht Q hQ hcsr
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'
  have hinj : Function.Injective (e.symm.toRingHom) := e.symm.injective
  have hQ'm : Q'.Monic := hQ.map _
  have hdeg : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective hinj _
  have hc := hcsr.resolve_left hw
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, map_zero, C_0, zero_mul] at hc
    exact (hQ.map (cj w)).ne_zero (reverse_eq_zero.mp hc.symm)
  have hQ'0 : Q'.coeff 0 ≠ 0 := by
    rw [hQ', coeff_map]
    exact fun h => hQ0 (hinj (by rw [h, map_zero]))
  let A := AdjoinRoot Q'
  let r : A := AdjoinRoot.root Q'
  let pb := AdjoinRoot.powerBasis' hQ'm
  haveI : Module.Finite K.E A := pb.finite
  have hr0 : aeval r Q' = 0 := by
    rw [aeval_def, AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.eval₂_root Q'
  set v : A := -(aeval r (divX Q')) * algebraMap K.E A (Q'.coeff 0)⁻¹ with hv
  have hrv : r * v = 1 := by
    have h1 := congrArg (aeval r) (X_mul_divX_add Q')
    rw [map_add (f := _), map_mul, aeval_X, aeval_C, hr0] at h1
    have h2 : algebraMap K.E A (Q'.coeff 0) * algebraMap K.E A (Q'.coeff 0)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hQ'0, map_one]
    linear_combination (-(algebraMap K.E A (Q'.coeff 0)⁻¹)) * h1 + h2
  letI : Invertible v := ⟨r, hrv, by rw [mul_comm]; exact hrv⟩
  have hce : ∀ y, K.c (e.symm y) = e.symm (cj w y) := by
    intro y; apply e.injective; rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hmapc : Q'.map K.c.toRingHom = (Q.map (cj w)).map e.symm.toRingHom := by
    rw [hQ', Polynomial.map_map, Polynomial.map_map]; congr 1; ext y; exact hce y
  have hrev : (Q'.map K.c.toRingHom).reverse = C (e.symm (cj w (Q.coeff 0))) * Q' := by
    rw [hmapc]
    unfold reverse
    rw [natDegree_map_eq_of_injective hinj, reflect_map, ← reverse, ← hc, Polynomial.map_mul, map_C]
    rfl
  have hev : eval₂ ((algebraMap K.E A).comp K.c.toRingHom) v Q' = 0 := by
    rw [← eval₂_map, ← eval₂_reverse_mul_pow (algebraMap K.E A) v, hrev]
    show eval₂ (algebraMap K.E A) r (C (e.symm (cj w (Q.coeff 0))) * Q') * _ = 0
    have hev0 : eval₂ (algebraMap K.E A) r Q' = 0 := by rw [← aeval_def]; exact hr0
    rw [eval₂_mul, hev0, mul_zero, zero_mul]
  let σ0 : A →+* A := AdjoinRoot.lift ((algebraMap K.E A).comp K.c.toRingHom) v hev
  have hσr : σ0 r = v := AdjoinRoot.lift_root hev
  have hσof : ∀ a, σ0 (algebraMap K.E A a) = algebraMap K.E A (K.c a) := fun a => AdjoinRoot.lift_of hev
  have hσv : σ0 v = r := by
    calc σ0 v = σ0 v * (r * v) := by rw [hrv, mul_one]
      _ = σ0 (r * v) * r := by rw [map_mul σ0 r v, hσr]; ring
      _ = r := by rw [hrv, map_one, one_mul]
  have hcomp : σ0.comp σ0 = RingHom.id A := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext
    · intro a
      show σ0 (σ0 (algebraMap K.E A a)) = algebraMap K.E A a
      rw [hσof, hσof]; simp [K.c_c]
    · show σ0 (σ0 r) = r
      rw [hσr, hσv]
  have hσσ : ∀ y, σ0 (σ0 y) = y := fun y => RingHom.congr_fun hcomp y
  let σ : A ≃+* A :=
    { toFun := σ0, invFun := σ0, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ0, map_add' := map_add σ0 }
  set tE : K.E := algebraMap K.O K.E t
  have htE : tE ≠ 0 := fun h => ht ((IsFractionRing.injective K.O K.E) (by rw [map_zero]; exact h))
  let B : GlobalTheory.UnitLemma.InvAlg K :=
    { A := A, σ := σ, σ_σ := hσσ, σ_alg := hσof, g := (r - 1) * algebraMap K.E A tE⁻¹ }
  have hu : (1 + algebraMap K.O B.A t * B.g) = r := by
    show (1 + algebraMap K.O A t * ((r - 1) * algebraMap K.E A tE⁻¹)) = r
    rw [IsScalarTower.algebraMap_apply K.O K.E A t]
    have h3 : algebraMap K.E A tE * algebraMap K.E A tE⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ htE, map_one]
    linear_combination (r - 1) * h3
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · rw [hu]; exact AdjoinRoot.adjoinRoot_eq_top
  · rw [hu]; exact hr0
  · show Module.finrank K.E A = Q.natDegree
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim, hdeg]
  · rw [hu]
    show r * σ0 r = 1
    rw [hσr, hrv]

end GlobalTheory.InvAlgConstr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply stalkLinear)

namespace GlobalTheory.VB.Ker

section Algebra

variable {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

theorem bijective_sumElim_iff {ι κ : Type} [Fintype ι] [Fintype κ] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (e : ι → M₁) (t : κ → M₂)
    (ht : Function.Bijective (Fintype.linearCombination R fun j => g (t j))) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t)) ↔
      Function.Bijective (Fintype.linearCombination R e) := by
  have h1 (a : ι ⊕ κ → R) : Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t) a =
      f (Fintype.linearCombination R e fun i => a (.inl i)) +
        Fintype.linearCombination R t fun j => a (.inr j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum]
  have h2 (b : κ → R) : g (Fintype.linearCombination R t b) =
      Fintype.linearCombination R (fun j => g (t j)) b := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Fintype.linearCombination_apply, map_sum]
  have h3 (b : κ → R) (m m' : M₁) (h : f m + Fintype.linearCombination R t b = f m') : b = 0 := by
    have := congrArg g h
    rw [map_add (f := _), hfg.apply_apply_eq_zero, hfg.apply_apply_eq_zero, zero_add, h2] at this
    exact ht.1 (this.trans (map_zero _).symm)
  constructor
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · have : Sum.elim a (0 : κ → R) = 0 := H.1 (by
        rw [h1, map_zero]
        change f (Fintype.linearCombination R e a) + Fintype.linearCombination R t 0 = 0
        rw [ha, map_zero, map_zero, add_zero])
      exact funext fun i => congrFun this (.inl i)
    · obtain ⟨a, ha⟩ := H.2 (f m)
      rw [h1] at ha
      rw [h3 _ _ _ ha, map_zero, add_zero] at ha
      exact ⟨_, hf ha⟩
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · rw [h1, ← map_zero f] at ha
      have hb := h3 _ _ _ ha
      rw [hb, map_zero, add_zero] at ha
      have ha' := H.1 ((hf ha).trans (map_zero _).symm)
      funext k
      rcases k with i | j
      exacts [congrFun ha' i, congrFun hb j]
    · obtain ⟨b, hb⟩ := ht.2 (g m)
      obtain ⟨n, hn⟩ := (hfg (m - Fintype.linearCombination R t b)).1 (by
        rw [map_sub, h2, hb, sub_self])
      obtain ⟨a, rfl⟩ := H.2 n
      exact ⟨Sum.elim a b, by rw [h1]; exact eq_sub_iff_add_eq.1 hn⟩

theorem nonempty_basis_of_exact [IsLocalRing R] {r s : ℕ} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (b : Module.Basis (Fin (r + s)) R M₂)
    (c : Module.Basis (Fin s) R M₃) : Nonempty (Module.Basis (Fin r) R M₁) := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis b
  have := Module.Finite.of_basis c
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨φ, hφ, -⟩ := hfg.splitSurjectiveEquiv hf ⟨σ, hσ⟩
  let π : M₂ →ₗ[R] M₁ := LinearMap.fst R M₁ M₃ ∘ₗ φ.toLinearMap
  have hπ : π ∘ₗ f = LinearMap.id := by
    ext m
    simp [π, hφ]
  have : Module.Projective R M₁ := .of_split f π hπ
  have : Module.Finite R M₁ := .of_surjective π fun m => ⟨f m, LinearMap.congr_fun hπ m⟩
  have : Module.Free R M₁ := Module.free_of_flat_of_isLocalRing
  have h := φ.finrank_eq
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c,
    Fintype.card_fin, Fintype.card_fin] at h
  exact ⟨Module.finBasisOfFinrankEq R M₁ (by omega)⟩

theorem bijective_iff_isUnit_det {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M₁)
    (v : ι → M₁) : Function.Bijective (Fintype.linearCombination R v) ↔ IsUnit (b.det v) := by
  rw [← Module.Basis.is_basis_iff_det, Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.range_eq_top, Fintype.range_linearCombination]

end Algebra

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem exists_germ_eq_family {x : X} (hx : x ∈ U) (a : ι → (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (e : ι → Γ(F, V)),
      ∀ i, F.presheaf.germ V x hV (e i) = a i := by
  choose W hW b hb using fun i => F.presheaf.exists_germ_eq (a i)
  have hxV : x ∈ U ⊓ Finset.univ.inf W := ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hW⟩
  have hV (i : ι) : U ⊓ Finset.univ.inf W ≤ W i :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  exact ⟨_, inf_le_left, hxV, fun i => resM F (hV i) (b i), fun i => by rw [germ_resM, hb]⟩

theorem germ_det [DecidableEq ι] {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U)) {x : X}
    (hx : x ∈ U) : X.presheaf.germ U x hx ((he.basis le_rfl).det v) =
      (he.stalkBasis x hx).det fun i => F.presheaf.germ U x hx (v i) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  refine (RingHom.map_det (X.presheaf.germ U x hx).hom _).trans ?_
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  conv_rhs => rw [← (he.basis le_rfl).sum_repr (v j)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, resM_self]
  simp only [← he.stalkBasis_apply x hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Module.Basis.repr_sum_self]
  rfl

theorem exists_isFrame_of_bijective_stalk {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U))
    {x : X} (hx : x ∈ U) (hv : Function.Bijective (Fintype.linearCombination (X.presheaf.stalk x)
      fun i => (F.presheaf.germ U x hx (v i) : (F.presheaf.stalk x :)))) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame fun i => resM F h (v i) := by
  classical
  rw [bijective_iff_isUnit_det (he.stalkBasis x hx), ← germ_det he] at hv
  refine ⟨X.basicOpen ((he.basis le_rfl).det v), X.basicOpen_le _,
    (X.mem_basicOpen _ x hx).2 hv, fun V h => ?_⟩
  simp only [resM_resM]
  rw [bijective_iff_isUnit_det (he.basis ((h.trans (X.basicOpen_le _)).trans le_rfl)),
    ← he.resG_det, ← resG_resG (X.basicOpen_le _) h]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _

end GlobalTheory.VB.Ker

namespace GlobalTheory.VB

open Ker

theorem isVB_X₁_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₂ (r + s) → IsVB S.X₃ s → IsVB S.X₁ r := by
  intro X S r s hS h₂ h₃ x
  have := hS.mono_f
  have := hS.epi_g
  have := h₂.isQuasicoherent
  have := h₃.isQuasicoherent
  obtain ⟨U₀, b₀, hx₀, hb₀⟩ := h₂ x
  obtain ⟨U, c, hU, hx, hle, hc⟩ := h₃.exists_affine hx₀
  choose t ht using fun j => QCoh.surjective_app_of_epi S.g hU (c j)
  have hex := (QCoh.exact_iff_stalkLinear S).1 hS.exact x
  obtain ⟨β⟩ := nonempty_basis_of_exact (QCoh.stalkLinear_injective S.f x) hex
    (QCoh.stalkLinear_surjective S.g x) (hb₀.stalkBasis x hx₀) (hc.stalkBasis x hx)
  obtain ⟨V, hV, hxV, e, he⟩ := exists_germ_eq_family hx β
  have hb := (hb₀.res (hV.trans hle)).comp_equiv finSumFinEquiv
  obtain ⟨W, hW, hxW, hv⟩ := exists_isFrame_of_bijective_stalk hb
    (Sum.elim (fun i => S.f.app V (e i)) fun j => resM S.X₂ hV (t j)) hxV (by
      have := (bijective_sumElim_iff (QCoh.stalkLinear_injective S.f x) hex β
        (fun j => S.X₂.presheaf.germ U x hx (t j)) (by
          simp only [QCoh.stalkLinear_germ, ht]
          exact hc.bijective_stalk x hx)).2 (by
          rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
            ← LinearMap.range_eq_top, Fintype.range_linearCombination]
          exact ⟨β.linearIndependent, β.span_eq⟩)
      convert this using 3
      funext k
      rcases k with i | j
      · rw [Sum.elim_inl, Sum.elim_inl, ← he, QCoh.stalkLinear_germ]
      · rw [Sum.elim_inr, Sum.elim_inr, germ_resM])
  refine ⟨W, fun i => resM S.X₁ hW (e i), hxW, fun T hT => ?_⟩
  refine (bijective_sumElim_iff (f := appLinear S.f T) (g := appLinear S.g T)
    (QCoh.injective_app_of_mono S.f T) (QCoh.exact_app_of_exact_of_mono hS.exact T) _
    (fun j => resM S.X₂ ((hT.trans hW).trans hV) (t j)) ?_).1 ?_
  · simp only [appLinear_apply, app_resM, ht]
    exact hc T _
  · convert hv T hT using 3
    funext k
    rcases k with i | j
    · simp only [Sum.elim_inl, appLinear_apply, app_resM]
    · simp only [Sum.elim_inr, resM_resM]

end GlobalTheory.VB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.DualExact

variable {X : Scheme.{0}}

theorem exists_local_section {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {s : ℕ} (hG : IsVB G s)
    {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens), U ≤ V ∧ x ∈ U ∧
      ∃ σ : ∀ W : X.Opens, W ≤ U → (Γ(G, W) →ₗ[Γ(X, W)] Γ(F, W)),
        (∀ (W W' : X.Opens) (h : W ≤ U) (h' : W' ≤ W) (t : Γ(G, W)),
          σ W' (h'.trans h) (resM G h' t) = resM F h' (σ W h t)) ∧
        ∀ (W : X.Opens) (h : W ≤ U) (t : Γ(G, W)), φ.app W (σ W h t) = t := by
  obtain ⟨U, e, -, hxU, hle, he⟩ := hG.exists_affine hx
  choose T hT hxT a ha using fun i => exists_app_eq_of_epi φ (e i) hxU
  let U' : X.Opens := U ⊓ Finset.univ.inf T
  have hx' : x ∈ U' := ⟨hxU, by rw [Opens.coe_finset_inf]; simpa using hxT⟩
  have hU' (i) : U' ≤ T i := inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  have hU : U' ≤ U := inf_le_left
  refine ⟨U', hU.trans hle, hx', fun W h =>
    (he.basis (h.trans hU)).constr Γ(X, W) fun i => resM F (h.trans (hU' i)) (a i),
    fun W W' h h' t => ?_, fun W h t => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
      resM_smul, resM_resM]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he.repr_resM (h.trans hU) h']
  · rw [← appLinear_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, map_sum,
      map_smul, appLinear_apply, app_resM, ha, resM_resM]
    conv_rhs => rw [← (he.basis (h.trans hU)).sum_repr t]
    simp only [IsFrame.basis_apply]

theorem exact_of_locally (S : ShortComplex X.Modules)
    (H : ∀ (V : X.Opens) (x : X), x ∈ V → ∃ U : X.Opens, U ≤ V ∧ x ∈ U ∧
      ∀ t : Γ(S.X₂, U), S.g.app U t = 0 → ∃ u, S.f.app U u = t) : S.Exact := by
  refine (QCoh.exact_iff_stalkLinear S).2 fun x t => ⟨fun ht => ?_, ?_⟩
  · obtain ⟨V, hV, t, rfl⟩ := S.X₂.presheaf.exists_germ_eq t
    rw [QCoh.stalkLinear_germ, ← map_zero (S.X₃.presheaf.germ V x hV).hom] at ht
    obtain ⟨V', hV', i₁, i₂, e⟩ := S.X₃.presheaf.germ_eq x hV hV _ _ ht
    have e' : resM S.X₃ i₁.le (S.g.app V t) = 0 := e.trans (map_zero _)
    obtain ⟨U, hU, hxU, HU⟩ := H V' x hV'
    obtain ⟨u, hu⟩ := HU (resM S.X₂ (hU.trans i₁.le) t) (by
      rw [app_resM, ← resM_resM i₁.le hU, e', map_zero])
    exact ⟨S.X₁.presheaf.germ U x hxU u, by rw [QCoh.stalkLinear_germ, hu, germ_resM]⟩
  · rintro ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, S.zero, QCoh.stalkLinear_zero,
      LinearMap.zero_apply]

theorem shortExact_dual : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (s : ℕ),
    S.ShortExact → IsVB S.X₃ s → (ShortComplex.mk (dualMap S.g) (dualMap S.f)
      (by rw [← dualMap_comp, S.zero, dualMap_zero])).ShortExact := by
  intro X S s hS h₃
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  have hinj (W : X.Opens) : Function.Injective (appLinear S.f W) :=
    QCoh.injective_app_of_mono S.f W
  refine ShortComplex.ShortExact.mk' (exact_of_locally _ fun V x hx => ?_)
    (mono_dualMap S.g) (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    refine ⟨U, hU, hxU, fun (l : Γ(dual S.X₂, U)) (hl : (dualMap S.f).app U l = 0) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ σ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hσ W W' h h', dualApp_resM]
    · refine dual_ext fun W h t => ?_
      change dualApp l h (σ W h (S.g.app W t)) = _
      obtain ⟨u, hu⟩ := hex W (t - σ W h (S.g.app W t)) (by rw [map_sub, hg, sub_self])
      have := dualApp_dualMap S.f l h u
      rw [hl, hu, map_sub, dualApp_zero, LinearMap.zero_apply, eq_comm, sub_eq_zero] at this
      exact this.symm
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := exists_local_section S.g h₃ hx
    let ρ (W : X.Opens) (h : W ≤ U) : Γ(S.X₂, W) →ₗ[Γ(X, W)] Γ(S.X₁, W) :=
      LinearMap.codRestrictOfInjective (LinearMap.id - σ W h ∘ₗ appLinear S.g W)
        (appLinear S.f W) (hinj W) fun t => hex W _ (by
          change S.g.app W (t - σ W h (S.g.app W t)) = 0
          rw [map_sub, hg, sub_self])
    have hρ (W : X.Opens) (h : W ≤ U) (t : Γ(S.X₂, W)) :
        S.f.app W (ρ W h t) = t - σ W h (S.g.app W t) :=
      LinearMap.codRestrictOfInjective_comp_apply _ (appLinear S.f W) _ _ t
    refine ⟨U, hxU, hU, fun (l : Γ(dual S.X₁, U)) =>
      ⟨dualMk (fun W h => dualApp l h ∘ₗ ρ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← dualApp_resM]
      congr 1
      apply hinj W'
      rw [appLinear_apply, appLinear_apply, app_resM, hρ, hρ, map_sub, app_resM, hσ W W' h h']
    · refine dual_ext fun W h u => ?_
      change dualApp l h (ρ W h (S.f.app W u)) = _
      congr 1
      apply hinj W
      rw [appLinear_apply, appLinear_apply, hρ, hz, map_zero, sub_zero]

end GlobalTheory.DualExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.UG

namespace GlobalTheory.ExpFrame

def rowProj (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (w : Fin N → ℕ) :
    dualWeyl O N N ν →ₗ[O] dualWeyl O N N ν :=
  (weightedHomogeneousComponent (rowW N N) w).restrict
    (fun x hx => dualWeylModuleRowGraded O N N ν w x hx)

theorem exists_unique_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (τ : ι)
    (w : Fin N → ℕ), ∃ a, IsProj O N lam τ w a ∧ ∀ a', IsProj O N lam τ w a' → a' = a := by
  intro O _ N ι _ _ lam τ w
  have hP : IsProj O N lam τ w (atFactor τ (rowProj O N (res N (lam τ)) w)) := by
    intro x y hy
    unfold atFactor
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext σ
    by_cases h : σ = τ
    · subst h
      simp only [Function.update_self, LinearMap.restrict_apply, rowProj]
      exact Subtype.ext hy.symm
    · simp [Function.update_of_ne h]
  refine ⟨_, hP, fun a' ha' => ?_⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  exact (ha' x y rfl).trans (hP x y rfl).symm

end GlobalTheory.ExpFrame

end
end

