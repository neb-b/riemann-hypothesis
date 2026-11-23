module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0273
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0279
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0286

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHecke
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensHkSum

open PositivityTheory.Rg.BcB.F.Tail.PExp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem extTensor_apply_eq (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (m : G × H) :
    extTensor ρ σ m = TensorProduct.map (ρ m.1) (σ m.2) := by
  rfl

theorem hkE_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ)
    (hs : {q : G ⧸ K | f q.out ≠ 0}.Finite) :
    hkE ρ K f = ∑ q ∈ hs.toFinset, f q.out • ρ q.out := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE
  apply finsum_eq_sum_of_support_subset
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h0
  exact hq (by simp [h0])

theorem map_sum_sum_apply {A B : Type} (s : Finset A) (t : Finset B) (a : A → ℂ) (b : B → ℂ)
    (P : A → Module.End ℂ V) (Q : B → Module.End ℂ W) (v : V ⊗[ℂ] W) :
    TensorProduct.map (∑ i ∈ s, a i • P i) (∑ j ∈ t, b j • Q j) v =
      ∑ p ∈ s ×ˢ t, (a p.1 * b p.2) • TensorProduct.map (P p.1) (Q p.2) v := by
  have hB : ∀ (P' : Module.End ℂ V) (Q' : Module.End ℂ W),
      TensorProduct.map P' Q' v = TensorProduct.mapBilinear (RingHom.id ℂ) V W V W P' Q' v := fun P' Q' => by
    rw [TensorProduct.mapBilinear_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hB, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_product,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem bijective_mk_out_prod (K : Subgroup G) (L : Subgroup H) :
    Function.Bijective (fun p : (G ⧸ K) × (H ⧸ L) =>
      (QuotientGroup.mk (p.1.out, p.2.out) : (G × H) ⧸ K.prod L)) := by
  constructor
  · rintro ⟨q1, r1⟩ ⟨q2, r2⟩ h
    simp only at h
    rw [QuotientGroup.eq, Subgroup.mem_prod] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at h1 h2
    have e1 : (QuotientGroup.mk q1.out : G ⧸ K) = QuotientGroup.mk q2.out := QuotientGroup.eq.mpr h1
    have e2 : (QuotientGroup.mk r1.out : H ⧸ L) = QuotientGroup.mk r2.out := QuotientGroup.eq.mpr h2
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at e1 e2
    rw [e1, e2]
  · intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨((QuotientGroup.mk x.1 : G ⧸ K), (QuotientGroup.mk x.2 : H ⧸ L)), ?_⟩
    simp only
    rw [QuotientGroup.eq, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    exact ⟨QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.1 : G ⧸ K)),
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.2 : H ⧸ L))⟩

theorem apply_out_mk {X : Type} (K : Subgroup G) (Φ : G → X) (hΦ : ∀ x, ∀ k ∈ K, Φ (x * k) = Φ x) (x : G) :
    Φ (QuotientGroup.mk x : G ⧸ K).out = Φ x := by
  have hk : x⁻¹ * (QuotientGroup.mk x : G ⧸ K).out ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x : G ⧸ K)).symm
  have e := hΦ x _ hk
  rw [mul_inv_cancel_left] at e
  exact e

theorem tensHk : TensHk := by
  intro G H V W _ _ _ _ _ _ ρ σ K L f e hf he hsf hse v hv
  have hfix : ∀ k ∈ K.prod L, extTensor ρ σ k v = v := by
    intro k hk
    have h1 := hv ⟨k, hk⟩
    simpa using h1
  have hinv : ∀ x : G × H, ∀ k ∈ K.prod L,
      (f (x * k).1 * e (x * k).2) • extTensor ρ σ (x * k) v = (f x.1 * e x.2) • extTensor ρ σ x v := by
    intro x k hk
    have hk' := Subgroup.mem_prod.mp hk
    rw [Prod.fst_mul, Prod.snd_mul, hf _ _ hk'.1, he _ _ hk'.2, map_mul, Module.End.mul_apply, hfix k hk]
  have key : (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v)
      = ∑ᶠ p : (G ⧸ K) × (H ⧸ L), (f p.1.out * e p.2.out) • TensorProduct.map (ρ p.1.out) (σ p.2.out) v := by
    rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_out_prod K L))]
    apply finsum_congr
    intro p
    rw [Equiv.ofBijective_apply]
    have h2 := apply_out_mk (K.prod L) (fun m : G × H => (f m.1 * e m.2) • extTensor ρ σ m v) hinv
      (p.1.out, p.2.out)
    simp only at h2
    rw [extTensor_apply_eq] at h2
    exact h2
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  show (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v) = _
  rw [key, hkE_eq_sum ρ K f hsf, hkE_eq_sum σ L e hse, map_sum_sum_apply]
  apply finsum_eq_sum_of_support_subset
  intro p hp
  rw [Function.mem_support] at hp
  rw [Finset.coe_product, Set.mem_prod, Set.Finite.coe_toFinset, Set.Finite.coe_toFinset,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · intro h0
    exact hp (by simp [h0])
  · intro h0
    exact hp (by simp [h0])

end GlobalTheory.CompanionTheory.TensHkSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquiv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.PiCoinv

section Modules

variable {α : Type} {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def pureSpan (K : ∀ a, Submodule ℂ (X a)) : Submodule ℂ (⨂[ℂ] a, X a) :=
  Submodule.span ℂ {t | ∃ (x : ∀ a, X a) (a : α), x a ∈ K a ∧ t = PiTensorProduct.tprod ℂ x}

theorem tprod_sub_mem [Fintype α] (K : ∀ a, Submodule ℂ (X a)) {x y : ∀ a, X a}
    (h : ∀ a, x a - y a ∈ K a) :
    PiTensorProduct.tprod ℂ x - PiTensorProduct.tprod ℂ y ∈ pureSpan K := by
  classical
  have key : ∀ s : Finset α, PiTensorProduct.tprod ℂ x -
      PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) ∈ pureSpan K := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro b s hb ih
      have hx : Function.update (fun a => if a ∈ s then y a else x a) b (x b) =
          (fun a => if a ∈ s then y a else x a) := by
        rw [Function.update_eq_self_iff]
        simp [hb]
      have hupd : (fun a => if a ∈ insert b s then y a else x a) =
          Function.update (fun a => if a ∈ s then y a else x a) b (y b) := by
        funext a
        by_cases hab : a = b
        · subst hab
          simp
        · simp [Function.update_of_ne hab, Finset.mem_insert, hab]
      have e : PiTensorProduct.tprod ℂ
            (Function.update (fun a => if a ∈ s then y a else x a) b (x b - y b)) =
          PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
            PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) := by
        rw [MultilinearMap.map_update_sub, hx, hupd]
      have hmem : PiTensorProduct.tprod ℂ (fun a => if a ∈ s then y a else x a) -
          PiTensorProduct.tprod ℂ (fun a => if a ∈ insert b s then y a else x a) ∈ pureSpan K := by
        rw [← e]
        exact Submodule.subset_span ⟨_, b, by simpa using h b, rfl⟩
      have := Submodule.add_mem _ ih hmem
      rwa [sub_add_sub_cancel] at this
  simpa using key Finset.univ

def rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) : X a :=
  Function.surjInv (Submodule.mkQ_surjective (K a)) (q a)

theorem mkQ_rep (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (a : α) :
    (K a).mkQ (rep K q a) = q a := by
  unfold rep
  exact Function.surjInv_eq (Submodule.mkQ_surjective (K a)) (q a)

def descendFun (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) : (⨂[ℂ] a, X a) ⧸ pureSpan K :=
  (pureSpan K).mkQ (PiTensorProduct.tprod ℂ (rep K q))

theorem descendFun_eq [Fintype α] (K : ∀ a, Submodule ℂ (X a)) (q : ∀ a, X a ⧸ K a) (y : ∀ a, X a)
    (hy : ∀ a, (K a).mkQ (y a) = q a) :
    descendFun K q = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ y) := by
  unfold descendFun
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact tprod_sub_mem K fun a => (Submodule.Quotient.eq _).1 ((mkQ_rep K q a).trans (hy a).symm)

theorem mkQ_update [DecidableEq α] (K : ∀ a, Submodule ℂ (X a)) {q : ∀ a, X a ⧸ K a} {y : ∀ a, X a}
    (hy : ∀ a, (K a).mkQ (y a) = q a) (a : α) {w : X a} {r : X a ⧸ K a} (hw : (K a).mkQ w = r) (b : α) :
    (K b).mkQ (Function.update y a w b) = Function.update q a r b := by
  by_cases hb : b = a
  · subst hb
    simp [hw]
  · simp [Function.update_of_ne hb, hy]

def descend [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    (Π a, X a ⧸ K a) →ₘₗ[ℂ] ((⨂[ℂ] a, X a) ⧸ pureSpan K) where
  toFun := descendFun K
  map_update_add' := by
    intro _ q a u v
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    obtain ⟨sv, hv⟩ := Submodule.mkQ_surjective (K a) v
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := su + sv) (by rw [map_add (f := _), hu, hv])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), descendFun_eq K _ _ (mkQ_update K hy a hv),
      MultilinearMap.map_update_add, map_add]
  map_update_smul' := by
    intro _ q a c u
    obtain ⟨su, hu⟩ := Submodule.mkQ_surjective (K a) u
    have hy := mkQ_rep K q
    rw [descendFun_eq K _ _ (mkQ_update K hy a (w := c • su) (by rw [map_smul, hu])),
      descendFun_eq K _ _ (mkQ_update K hy a hu), MultilinearMap.map_update_smul, map_smul]

def quotMap (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) →ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  (pureSpan K).liftQ (PiTensorProduct.map fun a => (K a).mkQ) (Submodule.span_le.2 (by
    rintro _ ⟨x, a, hx, rfl⟩
    show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ x) = 0
    rw [PiTensorProduct.map_tprod]
    exact MultilinearMap.map_coord_zero _ a ((Submodule.Quotient.mk_eq_zero _).2 hx)))

def quotEquiv [Fintype α] (K : ∀ a, Submodule ℂ (X a)) :
    ((⨂[ℂ] a, X a) ⧸ pureSpan K) ≃ₗ[ℂ] ⨂[ℂ] a, X a ⧸ K a :=
  LinearEquiv.ofLinear (quotMap K) (PiTensorProduct.lift (descend K))
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      show quotMap K (PiTensorProduct.lift (descend K) (PiTensorProduct.tprod ℂ q)) =
        PiTensorProduct.tprod ℂ q
      rw [PiTensorProduct.lift.tprod]
      show PiTensorProduct.map (fun a => (K a).mkQ) (PiTensorProduct.tprod ℂ (rep K q)) = _
      rw [PiTensorProduct.map_tprod]
      exact congrArg _ (funext (mkQ_rep K q)))
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      show PiTensorProduct.lift (descend K) (PiTensorProduct.map (fun a => (K a).mkQ)
        (PiTensorProduct.tprod ℂ x)) = (pureSpan K).mkQ (PiTensorProduct.tprod ℂ x)
      rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
      exact descendFun_eq K _ x fun _ => rfl)

end Modules

section Reps

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)]

theorem twKer_piTensor_le (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) ≤ pureSpan fun a => twKer (π a) (H a) (χ a) := by
  unfold twKer
  apply Submodule.span_le.2
  rintro _ ⟨n, v, rfl⟩
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.tprod ℂ (fun a => π a ((n : ∀ a, Γ a) a) (x a)) := by
      show PiTensorProduct.map (fun a => π a ((n : ∀ a, Γ a) a)) (PiTensorProduct.tprod ℂ x) = _
      rw [PiTensorProduct.map_tprod]
    have e2 : ((piChar χ n : ℂˣ) : ℂ) =
        ∏ a, ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ) := by
      rw [← Units.coe_prod]
      rfl
    have e3 := (MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ)
      (fun a => ((χ a ⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : ℂˣ) : ℂ)) x).symm
    simp only [RingHom.id_apply] at e3
    rw [map_smul, smul_comm, ← smul_sub]
    apply Submodule.smul_mem
    rw [e1, e2, e3]
    apply tprod_sub_mem
    intro a
    apply Submodule.subset_span
    exact ⟨⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩, x a, rfl⟩
  | add v₁ v₂ h₁ h₂ =>
    rw [map_add (f := _), smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h₁ h₂

theorem pureSpan_le_twKer (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    (pureSpan fun a => twKer (π a) (H a) (χ a)) ≤ twKer (piTensor π) (piSub H) (piChar χ) := by
  classical
  apply Submodule.span_le.2
  rintro _ ⟨x, a, hx, rfl⟩
  have key : ∀ u ∈ twKer (π a) (H a) (χ a),
      PiTensorProduct.tprod ℂ (Function.update x a u) ∈ twKer (piTensor π) (piSub H) (piChar χ) := by
    intro u hu
    unfold twKer at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, v, rfl⟩ := hu
      have hn : Pi.mulSingle a (g : Γ a) ∈ piSub H := by
        refine (Subgroup.mem_pi _).2 fun b _ => ?_
        by_cases hb : b = a
        · subst hb
          simp
        · rw [Pi.mulSingle_eq_of_ne hb]
          exact one_mem _
      let n : piSub H := ⟨Pi.mulSingle a (g : Γ a), hn⟩
      have e1 : (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) =
          PiTensorProduct.tprod ℂ (Function.update x a (π a (g : Γ a) v)) := by
        show PiTensorProduct.map (fun b => π b ((n : ∀ a, Γ a) b))
          (PiTensorProduct.tprod ℂ (Function.update x a v)) = _
        rw [PiTensorProduct.map_tprod]
        congr 1
        funext b
        by_cases hb : b = a
        · subst hb
          simp [n]
        · simp [n, Function.update_of_ne hb, Pi.mulSingle_eq_of_ne hb]
      have e2 : ((piChar χ n : ℂˣ) : ℂ) = ((χ a g : ℂˣ) : ℂ) := by
        have hu : (piChar χ n : ℂˣ) = ∏ b, χ b ⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ := rfl
        rw [hu, Finset.prod_eq_single a]
        · have : (⟨(n : ∀ a, Γ a) a, n.2 a (Set.mem_univ a)⟩ : H a) = g := Subtype.ext (by simp [n])
          rw [this]
        · intro b _ hb
          have : (⟨(n : ∀ a, Γ a) b, n.2 b (Set.mem_univ b)⟩ : H b) = 1 :=
            Subtype.ext (by simp [n, Pi.mulSingle_eq_of_ne hb])
          rw [this, map_one]
        · intro h
          exact absurd (Finset.mem_univ a) h
      have hw : PiTensorProduct.tprod ℂ (Function.update x a ((π a) (g : Γ a) v - ((χ a g : ℂˣ) : ℂ) • v)) =
          (piTensor π) (n : ∀ a, Γ a) (PiTensorProduct.tprod ℂ (Function.update x a v)) -
            ((piChar χ n : ℂˣ) : ℂ) • PiTensorProduct.tprod ℂ (Function.update x a v) := by
        rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, RingHom.id_apply, e1, e2]
      rw [hw]
      exact Submodule.subset_span ⟨n, _, rfl⟩
    | zero =>
      rw [MultilinearMap.map_update_zero]
      exact Submodule.zero_mem _
    | add u₁ u₂ _ _ h₁ h₂ =>
      rw [MultilinearMap.map_update_add]
      exact Submodule.add_mem _ h₁ h₂
    | smul c u _ h =>
      rw [MultilinearMap.map_update_smul]
      exact Submodule.smul_mem _ c h
  have := key (x a) hx
  rwa [Function.update_eq_self] at this

theorem twKer_piTensor_eq (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a))
    (χ : ∀ a, H a →* ℂˣ) :
    twKer (piTensor π) (piSub H) (piChar χ) = pureSpan fun a => twKer (π a) (H a) (χ a) := by
  exact le_antisymm (twKer_piTensor_le π H χ) (pureSpan_le_twKer π H χ)

end Reps

theorem twJacquet_piTensor_equiv : ∀ {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (Γ a) (X a)) (H : ∀ a, Subgroup (Γ a)) (χ : ∀ a, H a →* ℂˣ), Nonempty (TwJacquet (piTensor π) (piSub H) (piChar χ) ≃ₗ[ℂ] ⨂[ℂ] a, TwJacquet (π a) (H a) (χ a)) := by
  intro α _ Γ X _ _ _ π H χ
  exact ⟨(Submodule.quotEquivOfEq _ _ (twKer_piTensor_eq π H χ)).trans
    (quotEquiv fun a => twKer (π a) (H a) (χ a))⟩

end GlobalTheory.CompanionTheory.Rodier.PiCoinv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift


set_option maxHeartbeats 1000000 in
theorem exists_uniform_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  intro R _ _ I Y β hβ hP N v hN d hd m s hs
  obtain ⟨g, ρ, hρ⟩ : ∃ (g : ℕ) (ρ : Fin g → R), Ideal.span (Set.range ρ) = I := by
    obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨S.card, fun k => (S.equivFin.symm k : R), ?_⟩
    rw [← hS]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ (S.equivFin.symm k).2, fun hx => ⟨S.equivFin ⟨x, hx⟩, by simp⟩⟩
  subst hρ
  obtain ⟨D, hD0, hDβ, hDm, hDi, hDc, hDa⟩ :=
    _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower R _ Y β hβ (pw (N 0) (d : ℤ)) m s (isLB_pw (hN 0).1 _) hs
  obtain ⟨sh, hsh0, hshp, hshu⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R)
      (A := fun t => Tm _ Y N D (d : ℤ) e t S) fun j t => mulT _ Y N D (d : ℤ) e t S (sh e j S) :=
    fun e S i j t a => mulT_comm _ Y N D (d : ℤ) e t S (sh e i S) (sh e j S) a
  have hloc := GlobalTheory.T.formal_lift_sections_nonvanishing R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  have hDβ' : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have h_pres : ∀ e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) (e + 1) t S),
      S.Nonempty → red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S' (resT _ Y N D (d : ℤ) hDm (e + 1) t h a) =
        resT _ Y N D (d : ℤ) hDm e t h (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) :=
    fun e t S S' h a _ => _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
      (D (e + 1) S') (D e S) (D e S') (hDβ' e S) (hDβ' e S') (hDm (e + 1) S S' h)
      (hDm e S S' h) a
  have h_mp : ∀ j e t (S : Finset (Fin (m + 1))) (a : Tm _ Y N D (d : ℤ) (e + 1) t S), S.Nonempty →
      red _ Y N D β hβ v hN hDβ' ((d : ℤ) * (t + 1)) e S (mulT _ Y N D (d : ℤ) (e + 1) t S (sh (e + 1) j S) a) =
        mulT _ Y N D (d : ℤ) e t S (sh e j S) (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) := by
    intro j e t S a hS
    have h1 := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * t)
      (d : ℤ) ((d : ℤ) * (t + 1)) (by ring) e S ((SecOnR.of _ _ _).symm a) (sh (e + 1) j S)
    rw [hshp e j S hS] at h1
    exact h1
  have h_mres : ∀ j e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) e t S), S.Nonempty →
      resT _ Y N D (d : ℤ) hDm e (t + 1) h (mulT _ Y N D (d : ℤ) e t S (sh e j S) a) -
        mulT _ Y N D (d : ℤ) e t S' (sh e j S') (resT _ Y N D (d : ℤ) hDm e t h a) ∈
          Ideal.span (Set.range ρ) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e (t + 1) S')) :=
    fun j e t S S' h a hS => _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
      sh hsh0 hshp hshu j e t S S' h a hS
  have h_G3 : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) ∧
        LinearMap.ker (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤ :=
    fun e t S hS => _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)
  have h_kill : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e t S)) = ⊥ :=
    fun e t S _ => _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.pow_smul_top_secOnR R _ Y e _ _
  have h_bij : ∀ i e t (S : Finset (Fin (m + 1))), i ∈ S → Function.Bijective (mulT _ Y N D (d : ℤ) e t S (sh e i S)) := by
    intro i e t S hi
    obtain ⟨y, hy⟩ := hshu e i S hi
    exact _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse R _ Y β hβ N v hN (d : ℤ) (Fin (m + 1)) D e t S (sh e i S) y hy
  have h_one : ∀ e (i : Fin (m + 1)), red _ Y N D β hβ v hN hDβ' ((d : ℤ) * 0) e {i} (oneT _ Y N D (d : ℤ) (e + 1) {i}) =
      oneT _ Y N D (d : ℤ) e {i} :=
    fun e i => _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.red_oneOn R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * 0) (mul_zero _) e {i}
  have h_fin := GlobalTheory.T.formal_lift_closed_embedding R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.uniform_first_cohomology_kernels_exist (Fin (m + 1)) R g ρ (Tm _ Y N D (d : ℤ))
    (fun e t S S' h => resT _ Y N D (d : ℤ) hDm e t h)
    (fun e t S => red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S)
    (fun j e t S => mulT _ Y N D (d : ℤ) e t S (sh e j S))
    (fun e i => oneT _ Y N D (d : ℤ) e {i}) hc
    (fun e t S h a => SecOnR.restrict_self _ _ _)
    (fun e t S S' S'' h h' a => SecOnR.restrict_restrict _ _ _ _)
    h_pres h_mp h_mres (fun e t S hS => (h_G3 e t S hS).1) (fun e t S hS => (h_G3 e t S hS).2)
    h_kill h_bij hloc.1 hloc.2 h_one h_fin
  refine ⟨t₀.toNat, fun t ht D' hD' e σ => ?_⟩
  subst hD'
  exact _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa (t : ℤ) e
    (fun c hc0 hcoc => ht₀ t (by omega) e c hc0 hcoc) σ

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

