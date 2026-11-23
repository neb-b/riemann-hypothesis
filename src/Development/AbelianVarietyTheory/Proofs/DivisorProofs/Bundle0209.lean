module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HilbAff.IdealDet
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem comm_fst {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (str A B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    congrArg (fun f => f.hom a) h1
  have key : (str A B).appTop ≫ (pullback.fst (str A B) g).appLE ⊤
      ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) =
      g.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
    calc _ = (pullback.fst (str A B) g ≫ str A B).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = (pullback.snd (str A B) g ≫ g).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          appLE_eq_of_eq (by simp [pullback.condition]) _ _ _ _
      _ = _ := by
          rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h2, secAlg, RingHom.comp_apply, ← CommRingCat.comp_apply, key, CommRingCat.comp_apply]

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => comm_fst A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    (letI := (secAlg A g U).toAlgebra
     theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
       ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
         ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    (letI := (secAlg A g U).toAlgebra
     ∀ x : Γ(T, U) ⊗[A] B, kappa A B g I U x =
       (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x)) := by
  letI := (secAlg A g U).toAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; rfl
  | tmul c b =>
    change ((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
        ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = _
    rw [theta_tmul, map_mul]
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤ ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U)
          (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    congr 1
    rw [← e]; rfl

theorem theta_surjective {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (hU : IsAffineOpen U) : Function.Surjective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (str A B) g)
    inferInstance (isAffineOpen_top _) hU le_top (by simp)
  let R : CommRingCat.{0} := CommRingCat.of (Γ(T, U) ⊗[A] B)
  let k : Γ(T, U) ⟶ R := CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (S := A)).toRingHom
  let h : Γ(Spec (CommRingCat.of B), (str A B) ⁻¹ᵁ ⊤) ⟶ R :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U))).toRingHom
  have w : (str A B).app ⊤ ≫ h = g.appLE ⊤ U le_top ≫ k := by
    ext x
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = x :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom x, by simp⟩
    have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
    have h2 : (str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a) :=
      (congrArg (fun f => f.hom a) h1).symm
    change (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U)))
      ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ((str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      (Algebra.TensorProduct.includeLeft (S := A)) (secAlg A g U a)
    rw [h2, Iso.inv_hom_id_apply]
    exact ((Algebra.TensorProduct.includeRight).commutes a).trans
      ((Algebra.TensorProduct.includeLeft (S := A)).commutes a).symm
  let ψ := hP.desc h k w
  have hθ : ψ ≫ CommRingCat.ofHom (theta A B g U) = 𝟙 _ := by
    apply hP.hom_ext
    · rw [hP.inl_desc_assoc, Category.comp_id]
      ext z
      change theta A B g U ((1 : Γ(T, U)) ⊗ₜ[A] ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z)) = _
      have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z) = z :=
        Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) z
      rw [theta_tmul, map_one, one_mul, e]
      rfl
    · rw [hP.inr_desc_assoc, Category.comp_id]
      ext c
      change theta A B g U (c ⊗ₜ[A] (1 : B)) = _
      rw [theta_tmul, map_one, map_one, mul_one]
  intro y
  exact ⟨ψ y, congrArg (fun F => F.hom y) hθ⟩

theorem eq_of_ker_kappa_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) =
      RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  intro A B _ _ _ T g I₁ I₂ h
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback (str A B) g)
      (inferInstance : IsAffineHom (str A B))
  let W : T.affineOpens → (pullback (str A B) g).affineOpens :=
    fun U => ⟨pullback.snd (str A B) g ⁻¹ᵁ U, U.2.preimage _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ ?_
  · exact (pullback.snd (str A B) g).iSup_preimage_eq_top (iSup_affineOpens_eq_top T)
  · intro U
    letI := (secAlg A g U).toAlgebra
    have key : ∀ I : (pullback (str A B) g).IdealSheafData,
        I.ideal (W U) = Ideal.map (theta A B g U) (RingHom.ker (kappa A B g I U)) := by
      intro I
      have e : RingHom.ker (kappa A B g I U) = Ideal.comap (theta A B g U) (I.ideal (W U)) := by
        ext x
        rw [RingHom.mem_ker, Ideal.mem_comap, ← I.ker_subschemeι_app (W U), RingHom.mem_ker,
          kappa_apply]
        rfl
      rw [e, Ideal.map_comap_of_surjective _ (theta_surjective A B g U U.2)]
    rw [key, key, h U]

end GlobalTheory.HilbAff.IdealDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTensorEqZeroOrOneOfIsPurelyInseparableStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' : ∀ (k K B : Type) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B] (e : K ⊗[k] B), IsIdempotentElem e → e = 0 ∨ e = 1 := by
  first | exact @GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | exact GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable | (intros; apply GlobalTheory.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIsDomainIsIntegrallyClosed
section
open IsLocalRing

namespace GlobalTheory

namespace IndEtaleNormal

open Polynomial

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

lemma exists_mem_of_finset (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (T : Finset S) : ∃ i, ∀ t ∈ T, t ∈ Si i := by
  classical
  choose idx hidx using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (T.image idx)
  exact ⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩

lemma isDomain [Nontrivial S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (hdom : ∀ i, IsDomain (Si i)) : IsDomain S := by
  classical
  have : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov {x, y}
    have hx : x ∈ Si i := hi x (by simp)
    have hy : y ∈ Si i := hi y (by simp)
    haveI := hdom i
    have h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0 := Subtype.ext (by simpa using hxy)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact NoZeroDivisors.to_isDomain S

lemma isIntegrallyClosed [IsDomain S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i)
    (hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))
  haveI := (hic i).1
  haveI := (hic i).2
  have ha : a ∈ Si i := hi a (by simp)
  have hb' : b ∈ Si i := hi b (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S)
    with hg_def
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (Si i) →+* FractionRing S := IsFractionRing.lift hg
  have hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c := fun c =>
    IsFractionRing.lift_algebraMap hg c
  have hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ /
    algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def
  have hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b := by
    rw [hy_def, map_div₀, hφ, hφ]
    rfl
  have hyint : IsIntegral (Si i) y := by
    refine ⟨q, hqm, φ.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hφy]
    have : φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g :=
      RingHom.ext hφ
    rw [this, hg_def, ← Polynomial.eval₂_map, hq]
    exact hp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint
  refine ⟨(c : S), ?_⟩
  rw [← hφy, ← hc, hφ]
  rfl

end IndEtaleNormal

theorem indEtale_isDomain_isIntegrallyClosed :
    ∀ (R S : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S]
      [Nontrivial S], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
        ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
          (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) →
      IsDomain S ∧ IsIntegrallyClosed S := by
  intro R S _ _ _ _ _ _ h
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := h
  have hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    obtain ⟨h1, h2⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R A q
    exact ⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)
  exact ⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveAndSaturatedOfInjectiveModRegular
section
open IsLocalRing

namespace GlobalTheory

theorem injective_and_saturated_of_injective_mod_regular :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Type) [CommRing A]
      [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] (f : R),
      f ∈ maximalIdeal R → IsSMulRegular B f → ∀ ψ : A →ₐ[R] B,
      (∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
        a ∈ (Ideal.span {f}).map (algebraMap R A)) →
      Function.Injective ψ ∧ ∀ b : B, f • b ∈ ψ.range → b ∈ ψ.range := by
  intro R _ _ _ A B _ _ _ _ _ f hf hreg ψ hψ

  have memA : ∀ a : A, a ∈ (Ideal.span {f}).map (algebraMap R A) → ∃ c : A, a = f • c := by
    intro a ha
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_comm]⟩
  have memB : ∀ b : B, f • b ∈ (Ideal.span {f}).map (algebraMap R B) := by
    intro b
    rw [Ideal.map_span, Set.image_singleton, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : A, a = f • c :=
    fun a h => memA a (hψ a h)
  refine ⟨?_, ?_⟩
  ·
    set K : Submodule R A := LinearMap.ker ψ.toLinearMap with hK
    have hFG : K.FG := IsNoetherian.noetherian K
    have hle : K ≤ Ideal.span {f} • K := by
      intro a ha
      have ha0 : ψ a = 0 := ha
      obtain ⟨c, rfl⟩ := key a (by rw [ha0]; exact Submodule.zero_mem _)
      have hc : ψ c = 0 := by
        apply hreg
        change f • ψ c = f • (0 : B)
        rw [smul_zero, ← map_smul]
        exact ha0
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) hc
    have hjac : Ideal.span {f} ≤ Ideal.jacobson (⊥ : Ideal R) := by
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hf
    have hK0 : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ K hFG hle hjac
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ K := ha
    rw [hK0] at this
    exact (Submodule.mem_bot R).1 this
  · intro b ⟨a, ha'⟩
    have ha : ψ a = f • b := ha'
    obtain ⟨c, rfl⟩ := key a (by rw [ha]; exact memB b)
    refine ⟨c, ?_⟩
    apply hreg
    change f • ψ c = f • b
    rw [← map_smul, ha]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementCentral
section
open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_central : ∀ {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ),
    (∀ a b, s (a * b) = s b * s a) → (∀ a, s (s a) = a) → (∀ a b, φ (a * b) = φ (b * a)) →
    (∀ a, φ (s a) = φ a) → (∀ a, a ≠ 0 → 0 < φ (s a * a)) →
    ∀ a, a * casimir (⇑x) s φ = casimir (⇑x) s φ * a := by
  intro O _ r x s φ hs hss hφc hφs hpos a
  classical
  set b := form s φ with hbdef
  have hb : ∀ u v, b u v = b v u := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hGdef
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := adjugate_gram_symm hs hss hφs
  have hds : ∀ v, G.det • v = ∑ i, ∑ j, (G.adjugate i j * b (x i) v) • x j :=
    det_smul_eq_sum x b hb
  have hδ : G.det ≠ 0 := by
    have h := (posDef_gram x b hb (fun w hw => hpos w hw)).det_pos
    rw [← Int.cast_det] at h
    exact_mod_cast h.ne'
  haveI : Module.Free ℤ O := Module.Free.of_basis x
  have htf : Function.Injective (fun v : O => G.det • v) := smul_right_injective O hδ
  have hbid : ∀ u v, b u (v * s a) = b v (u * a) := by
    intro u v
    rw [hb v]
    simp only [hbdef, form_apply]
    rw [hs, ← mul_assoc, hφc, ← mul_assoc]
  set A := G.adjugate with hAdef
  set F : Fin r → Fin r → Fin r → Fin r → O :=
    fun i j k l => (A i j * (A k l * b (x k) (x i * s a))) • (s (x l) * x j) with hF
  have key1 : ∀ i j, G.det • (A i j • (a * (s (x i) * x j))) = ∑ k, ∑ l, F i j k l := by
    intro i j
    have e : a * (s (x i) * x j) = s (x i * s a) * x j := by rw [hs, hss, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, smul_comm, show G.det • (s (x i * s a) * x j) = s (G.det • (x i * s a)) * x j by
      rw [map_zsmul, smul_mul_assoc], hds, map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, smul_mul_assoc, smul_smul]
  have key2 : ∀ p q, G.det • (A p q • (s (x p) * x q * a)) = ∑ i, ∑ j, F i j q p := by
    intro p q
    rw [smul_comm, mul_assoc, ← mul_smul_comm, hds, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul, hF, hA p q, ← hbid]
    ring_nf
  apply htf
  simp only
  have L : G.det • (a * casimir (⇑x) s φ) = ∑ i, ∑ j, ∑ k, ∑ l, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, key1]
  have R : G.det • (casimir (⇑x) s φ * a) = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := by
    unfold casimir
    rw [← hGdef, ← hAdef, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_mul_assoc, key2]
  rw [L, R]
  calc ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, ∑ j, F i j k l := Finset.sum_comm

end GlobalTheory.CasimirOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementMulPos
section
open GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

open Matrix

theorem casimir_mul_pos {O : Type} [Ring O] {r : ℕ} (x : Module.Basis (Fin r) ℤ O) (s : O →+ O)
    (φ : O →+ ℤ) (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (_hφc : ∀ a b, φ (a * b) = φ (b * a)) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a)) :
    ∀ u, u ≠ 0 → 0 < φ (s (casimir (⇑x) s φ * u) * u) := by
  intro u hu
  classical
  set A := (gram (⇑x) s φ).adjugate with hA
  set y : Fin r → O := fun i => x i * u with hy
  set H : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => ((form s φ (y i) (y j) : ℤ) : ℝ) with hHdef
  have key : φ (s (casimir (⇑x) s φ * u) * u) = ∑ i, ∑ j, A i j * form s φ (y j) (y i) := by
    rw [hs]
    unfold casimir
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, hs, hss, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
      smul_mul_assoc, form_apply, hy, smul_eq_mul, hA]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc]
  have hnn : ∀ w, 0 ≤ form s φ w w := by
    intro w
    by_cases hw : w = 0
    · simp [hw]
    · exact (hp w hw).le
  have hHpsd : H.PosSemidef := GlobalTheory.gram_posSemidef_of_int_form (form s φ) (form_symm hs hss hφs) hnn y
  have hP : (A.map (Int.cast : ℤ → ℝ)).PosDef := by
    have h1 := posDef_gram x (form s φ) (form_symm hs hss hφs) (fun w hw => by simpa using hp w hw)
    have e : A.map (Int.cast : ℤ → ℝ) = ((Matrix.of fun i j : Fin r => form s φ (x i) (x j)).map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hA, gram_eq]
      exact (RingHom.map_adjugate (Int.castRingHom ℝ) (Matrix.of fun i j : Fin r => form s φ (x i) (x j)))
    rw [e]
    exact adjugate_posDef h1
  have hy0 : ∃ i, y i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    calc u = (∑ i, x.repr 1 i • x i) * u := by rw [x.sum_repr, one_mul]
      _ = ∑ i, x.repr 1 i • y i := by rw [Finset.sum_mul]; simp only [hy, smul_mul_assoc]
      _ = 0 := by simp [h]
  have hH0 : H ≠ 0 := by
    obtain ⟨i, hi⟩ := hy0
    intro h
    have h3 := hp _ hi
    have h2 := congrFun (congrFun h i) i
    rw [hHdef] at h2
    simp only [of_apply, form_apply, Matrix.zero_apply, Int.cast_eq_zero] at h2
    omega
  have ht := trace_mul_pos_real hP hHpsd hH0
  have e : (A.map (Int.cast : ℤ → ℝ) * H).trace = ((∑ i, ∑ j, A i j * form s φ (y j) (y i) : ℤ) : ℝ) := by
    simp [Matrix.trace, Matrix.mul_apply, hHdef]
  rw [e] at ht
  rw [key]
  exact_mod_cast ht

end GlobalTheory.CasimirOrder
end

