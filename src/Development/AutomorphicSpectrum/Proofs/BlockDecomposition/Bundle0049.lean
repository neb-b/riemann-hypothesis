module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfLTensorSubtypeEqZero
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_eq_zero_of_lTensor_subtype_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type)
      [AddCommGroup N] [Module R N] (K : Type) [AddCommGroup K] [Module R K] (I : Submodule R K),
      (∀ (a : R) (x : K), a ≠ 0 → a • x ∈ I → ∀ k, r k • x ∈ I) →
      ∀ w : N ⊗[R] I, I.subtype.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ _ _ r N _ _ K _ _ I hI w hw k
  let I' : Submodule R K :=
    { carrier := {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ I}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        rw [smul_add]
        refine I.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact I.smul_mem _ hax
        · rw [mul_smul]; exact I.smul_mem _ hby
      smul_mem' := by
        rintro c x ⟨a, ha, hax⟩
        refine ⟨a, ha, ?_⟩
        rw [smul_comm]; exact I.smul_mem _ hax }
  have hle : I ≤ I' := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  have hflat : Module.Flat R (K ⧸ I') := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := I'.mkQ_surjective y
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hy
    have hax : (a : R) • x ∈ I' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using ha
    obtain ⟨b, hb, hbx⟩ := hax
    have hx : x ∈ I' := ⟨b * a, mul_ne_zero hb (nonZeroDivisors.ne_zero a.2), by
      rw [mul_smul]; exact hbx⟩
    simpa using (Submodule.Quotient.mk_eq_zero I').2 hx
  have hinj : Function.Injective (I'.subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat I'.mkQ I'.mkQ_surjective I'.subtype
      I'.injective_subtype (LinearMap.exact_subtype_mkQ I') N
  let ι : I →ₗ[R] I' := Submodule.inclusion hle
  let φ : I' →ₗ[R] I := LinearMap.codRestrict I (r k • I'.subtype) (fun x => by
    obtain ⟨a, ha, hax⟩ := x.2
    exact hI a x ha hax k)
  have h1 : ι.lTensor N w = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    exact hw
  have hcomp : φ ∘ₗ ι = r k • LinearMap.id := by
    ext x
    rfl
  have h2 : φ.lTensor N (ι.lTensor N w) = r k • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_smul,
      LinearMap.lTensor_id]
    rfl
  rw [← h2, h1, map_zero]

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulSmulMemRange
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem smul_smul_mem_range {A B D K₁ K₀ : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup D] [Module A D] [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (ρ : B →ₗ[A] D) (hρ : Function.Surjective ρ) (h1 : ρ 1 = 0) (d : K₁ →ₗ[A] K₀) (s : A)
    (hGood : ∀ x : D ⊗[A] K₁, d.lTensor D x = 0 →
      ∃ v : D ⊗[A] LinearMap.ker d, (LinearMap.ker d).subtype.lTensor D v = s • x)
    (hK₁ : ∀ w : B ⊗[A] K₁, ρ.rTensor K₁ w = 0 → ∃ a : K₁, w = (1 : B) ⊗ₜ[A] a)
    (hK₀ : ∀ a : K₀, (1 : B) ⊗ₜ[A] a = 0 → s • a = 0)
    (z : K₀) (w : B ⊗[A] K₁) (hw : (1 : B) ⊗ₜ[A] z = d.lTensor B w) :
    s • s • z ∈ LinearMap.range d := by
  have comm₁ : ∀ t : B ⊗[A] K₁, d.lTensor D (ρ.rTensor K₁ t) = ρ.rTensor K₀ (d.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have comm₂ : ∀ t : B ⊗[A] LinearMap.ker d,
      (LinearMap.ker d).subtype.lTensor D (ρ.rTensor _ t)
        = ρ.rTensor K₁ ((LinearMap.ker d).subtype.lTensor B t) := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have dker : ∀ t : B ⊗[A] LinearMap.ker d,
      d.lTensor B ((LinearMap.ker d).subtype.lTensor B t) = 0 := by
    intro t
    induction t with
    | tmul b k => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
  have hw' : d.lTensor D (ρ.rTensor K₁ w) = 0 := by
    rw [comm₁, ← hw]; simp [h1]
  obtain ⟨v', hv'⟩ := hGood _ hw'
  obtain ⟨v, rfl⟩ := LinearMap.rTensor_surjective (LinearMap.ker d) hρ v'
  obtain ⟨u, hu⟩ := hK₁ (s • w - (LinearMap.ker d).subtype.lTensor B v) (by
    rw [map_sub, map_smul, ← comm₂, hv', sub_self])
  have key : (1 : B) ⊗ₜ[A] (d u - s • z) = 0 := by
    have := congrArg (d.lTensor B) hu
    rw [map_sub, map_smul, dker, sub_zero, ← hw, LinearMap.lTensor_tmul] at this
    rw [TensorProduct.tmul_sub, ← this, TensorProduct.tmul_smul, sub_self]
  have h := hK₀ _ key
  refine ⟨s • u, ?_⟩
  rw [map_smul]
  rw [smul_sub, sub_eq_zero] at h
  exact h

theorem pow_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (N : Submodule A M)
    {p : ℕ} (hp : 2 ≤ p) (s : A) (z : M) (h : s • s • z ∈ N) : s ^ p • z ∈ N := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have : s ^ (2 + q) • z = s ^ q • s • s • z := by
    simp only [smul_smul]; congr 1; ring
  rw [this]
  exact N.smul_mem _ h

theorem mv_cov : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ : B →ₗ[A] D), IsRt p r → Pf p D → Function.Surjective ρ → ρ 1 = 0 → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ w : B ⊗[A] K, ρ.rTensor K w = 0 → ∃ a : K, w = (1 : B) ⊗ₜ[A] a) → Cov p r B := by
  intro p _ A _ B _ _ D _ _ r ρ hr hD hρ h1 hK K₁ K₀ _ _ _ _ hp₁ hp₀ d hG z hz k
  obtain ⟨w, hw⟩ := hz
  have hmem : r (k + 1) • r (k + 1) • z ∈ LinearMap.range d :=
    smul_smul_mem_range ρ hρ h1 d (r (k + 1))
      (fun x hx => by
        obtain ⟨v, hv⟩ := hG D hD x hx (k + 1)
        exact ⟨v, hv⟩)
      (hK K₁ hp₁).2
      (fun a ha => (hK K₀ hp₀).1 a ha (k + 1))
      z w hw.symm
  rw [← hr k]
  exact pow_smul_mem _ (Fact.out : p.Prime).two_le _ _ hmem

end GlobalTheory.CompanionTheory.SnakeCov
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolvAtStage
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SeqColim

theorem map_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, x => rfl
  | k + 1, x => by
      show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
      rw [h.comm, map_tr f ι h n k x]

theorem pf_of_stages (p : ℕ) {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (hG : ∀ n, Pf p (G n)) : Pf p L := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ι 0) (hG 0).char
    simpa using this
  · intro x y hxy
    obtain ⟨n, z, hz⟩ := h.surj 2 ![x, y]
    have h0 : ι n (z 0 ^ p - z 1 ^ p) = 0 := by
      have e0 := hz 0
      have e1 := hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      simp [map_sub, map_pow, e0, e1, hxy]
    obtain ⟨k, hk⟩ := h.ker n 1 (fun _ => z 0 ^ p - z 1 ^ p) (fun _ => h0)
    have hk0 := hk 0
    simp only [map_sub, map_pow, sub_eq_zero] at hk0
    have heq := (hG (n + k)).bij.1 hk0
    have e0 := hz 0
    have e1 := hz 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have := congrArg (ι (n + k)) heq
    rw [map_tr f ι h, map_tr f ι h, e0, e1] at this
    exact this
  · intro x
    obtain ⟨n, z, hz⟩ := h.surj 1 (fun _ => x)
    obtain ⟨w, hw⟩ := (hG n).bij.2 (z 0)
    refine ⟨ι n w, ?_⟩
    simp only at hw ⊢
    rw [← map_pow, hw, hz 0]

theorem solv_at_stage {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A) (hs : Solv L a c) :
    ∃ N, Solv (G N) a c := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨N₀, z, hz⟩ := h.surj n y
  have hd : ∀ i, ι N₀ ((∑ j, a i j • z j) - algebraMap A (G N₀) (c i)) = 0 := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, AlgHom.commutes, hz, hy i, sub_self]
  obtain ⟨k, hk⟩ := h.ker N₀ m _ hd
  refine ⟨N₀ + k, fun j => tr f N₀ k (z j), fun i => ?_⟩
  have := hk i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, AlgHom.commutes, sub_eq_zero] at this
  exact this

end GlobalTheory.CompanionTheory.SeqColim

namespace GlobalTheory.CompanionTheory

theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := by
  intro p _ A _ G _ _ f L _ _ ι h
  exact ⟨SeqColim.pf_of_stages p f ι h, fun m n a c hs => SeqColim.solv_at_stage f ι h m n a c hs⟩

end GlobalTheory.CompanionTheory
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHolds
section
namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {G : Type} [Group G] {P Δ Γ : Subgroup G}

def cls (y : Γ) : Cos P Γ := Quotient.mk _ y

theorem cls_eq {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by
  unfold cls
  rw [Quotient.eq]
  show QuotientGroup.rightRel _ a b ↔ _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem rep_mem (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem cls_rep (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := Quotient.out_eq q

theorem rep_cls (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by
  have h : (cls y : Cos P Γ) = cls ⟨rep (cls y : Cos P Γ), rep_mem _⟩ := (cls_rep _).symm
  refine ⟨rep (cls y : Cos P Γ) * (y : G)⁻¹, cls_eq.1 h, Γ.mul_mem (rep_mem _) (Γ.inv_mem y.2), by group⟩

noncomputable def glue (hΔ : Δ ≤ Γ) (s : (_ : Cos Δ Γ) × Cos P Δ) : Cos P Γ :=
  cls ⟨rep s.2 * rep s.1, Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)⟩

theorem glue_injective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Injective (glue (P := P) hΔ) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ h
  have h1 : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ P := cls_eq.1 h
  have hΓ : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _))
      (Γ.inv_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)))
  have h2 := hP _ hΓ h1
  have h3 : rep r' * (rep r)⁻¹ ∈ Δ := by
    have : rep r' * (rep r)⁻¹ = (rep q')⁻¹ * (rep q' * rep r' * (rep q * rep r)⁻¹) * rep q := by
      group
    rw [this]
    exact Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (rep_mem _)) h2) (rep_mem _)
  have hr : r = r' := by
    rw [← cls_rep r, ← cls_rep r']
    exact cls_eq.2 h3
  subst hr
  have h4 : rep q' * (rep q)⁻¹ ∈ P := by
    have : rep q' * (rep q)⁻¹ = rep q' * rep r * (rep q * rep r)⁻¹ := by group
    rw [this]
    exact h1
  have hq : q = q' := by
    rw [← cls_rep q, ← cls_rep q']
    exact cls_eq.2 h4
  subst hq
  rfl

theorem glue_surjective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Surjective (glue (P := P) hΔ) := by
  intro t
  obtain ⟨y, rfl⟩ : ∃ y : Γ, cls y = t := ⟨_, cls_rep t⟩
  obtain ⟨d, hdΔ, -, hd⟩ := rep_cls (P := Δ) y
  obtain ⟨p, hpP, hpΔ, hp⟩ := rep_cls (P := P) (⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Δ)
  refine ⟨⟨cls y, cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩⟩, ?_⟩
  apply cls_eq.2
  show (y : G) * (rep (cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Cos P Δ) * rep (cls y : Cos Δ Γ))⁻¹ ∈ P
  rw [hp, hd]
  have : (y : G) * (p * d⁻¹ * (d * y))⁻¹ = p⁻¹ := by group
  rw [this]
  exact P.inv_mem hpP

theorem f_rep {X : Type} {f : G → X} (hf : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) (y : Γ) (g : G) :
    f (rep (cls y : Cos P Γ) * g) = f (y * g) := by
  obtain ⟨p, hpP, hpΓ, hp⟩ := rep_cls (P := P) y
  rw [hp, mul_assoc, hf p hpΓ hpP]

theorem stage : PiLocalization₂ := by
  intro G _ X _ _ P Δ Γ f hΔ hP hf g hs
  have hmem : ∀ (q : Cos P Δ) (x : G), x ∈ Γ → rep q * x ∈ Γ := fun q x hx =>
    Γ.mul_mem (hΔ (rep_mem q)) hx

  have h1 : ∀ x ∈ Γ, Summable fun q : Cos P Δ => ‖f (rep q * (x * g))‖ := by
    intro x hx
    have hinj : Function.Injective fun q : Cos P Δ => (cls ⟨rep q * x, hmem q x hx⟩ : Cos P Γ) := by
      intro q q' h
      have h1 : rep q' * x * (rep q * x)⁻¹ ∈ P := cls_eq.1 h
      have h2 : rep q' * (rep q)⁻¹ ∈ P := by
        have : rep q' * (rep q)⁻¹ = rep q' * x * (rep q * x)⁻¹ := by group
        rw [this]
        exact h1
      rw [← cls_rep q, ← cls_rep q']
      exact cls_eq.2 h2
    refine (hs.comp_injective hinj).congr fun q => ?_
    simp only [Function.comp_apply]
    rw [f_rep hf, mul_assoc]

  let e : ((_ : Cos Δ Γ) × Cos P Δ) ≃ Cos P Γ :=
    Equiv.ofBijective (glue hΔ) ⟨glue_injective hΔ hP, glue_surjective hΔ hP⟩
  let φ : ((_ : Cos Δ Γ) × Cos P Δ) → X := fun s => f (rep s.2 * (rep s.1 * g))
  have hφ : ∀ s, f (rep (e s) * g) = φ s := by
    intro s
    show f (rep (glue hΔ s) * g) = _
    unfold glue
    rw [f_rep hf, mul_assoc]
  have hn : Summable fun s => ‖φ s‖ := by
    refine ((e.summable_iff (f := fun q : Cos P Γ => ‖f (rep q * g)‖)).2 hs).congr fun s => ?_
    simp only [Function.comp_apply]
    rw [hφ]
  have hsig := (summable_sigma_of_nonneg (fun s => norm_nonneg (φ s))).1 hn
  have hφs : Summable φ := hn.of_norm
  refine ⟨h1, hsig.2, ?_⟩
  have hfib : ∀ r, Summable fun q : Cos P Δ => φ ⟨r, q⟩ := fun r => (hsig.1 r).of_norm
  calc ∑' q : Cos P Γ, f (rep q * g) = ∑' s, f (rep (e s) * g) := (e.tsum_eq _).symm
    _ = ∑' s, φ s := tsum_congr hφ
    _ = ∑' r : Cos Δ Γ, ∑' q : Cos P Δ, φ ⟨r, q⟩ := hφs.tsum_sigma' hfib

end GlobalTheory.CompanionTheory.RgEis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEvalFixedOfFixed
section
open TensorProduct CrystallineSemistableComparison.Pb.Psi

namespace GlobalTheory.CompanionTheory.FrobFix

theorem extension_fixed : ∀ {W C₀ : Type} [CommRing W] [CommRing C₀] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (k : K₀ →+* C₀) {B : Type} [Field B] [IsFractionRing W K₀] (ι : C₀ →+* B) (σB : B →+* B) (h : L →+ B) (E : K₀ ⊗[W] L →+ B), (∀ x y, E (x ⊗ₜ y) = ι (k x) * h y) → (∀ w, σB (ι (k (algebraMap W K₀ w))) = ι (k (algebraMap W K₀ w))) → (∀ y, σB (h y) = h y) → ∀ v : K₀ ⊗[W] L, σB (E v) = E v := by
  intro W C₀ _ _ K₀ _ _ L _ _ k B _ _ ι σB h E hE hW hy v
  have hinj : Function.Injective (ι.comp k) := (ι.comp k).injective
  have hg : ∀ x : K₀, σB (ι (k x)) = ι (k x) := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    have hb0 : algebraMap W K₀ b ≠ 0 :=
      (IsLocalization.map_units K₀ (⟨b, hb⟩ : nonZeroDivisors W)).ne_zero
    have hgb : ι (k (algebraMap W K₀ b)) ≠ 0 := by
      intro h0
      apply hb0
      apply hinj
      simpa using h0
    have hmul : ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b))
        = ι (k (algebraMap W K₀ a)) := by
      rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hb0]
    apply mul_right_cancel₀ hgb
    calc σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * ι (k (algebraMap W K₀ b))
        = σB (ι (k (algebraMap W K₀ a / algebraMap W K₀ b))) * σB (ι (k (algebraMap W K₀ b))) := by
          rw [hW b]
      _ = σB (ι (k (algebraMap W K₀ a))) := by rw [← map_mul, hmul]
      _ = ι (k (algebraMap W K₀ a)) := hW a
      _ = ι (k (algebraMap W K₀ a / algebraMap W K₀ b)) * ι (k (algebraMap W K₀ b)) := hmul.symm
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hE, map_mul, hg, hy]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

end GlobalTheory.CompanionTheory.FrobFix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TmulEqZeroOfMemSpan
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.TensCompl

theorem tmul_eq_zero_of_mem_span {R N A : Type} [CommRing R] [AddCommGroup N] [Module R N]
    [CommRing A] [Algebra R A] (c : R) (M : ℕ) (hN : ∀ x : N, c ^ M • x = 0) (n : N) (a : A)
    (ha : a ∈ Ideal.span {algebraMap R A c ^ M}) : n ⊗ₜ[R] a = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have : b * algebraMap R A c ^ M = c ^ M • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this, ← smul_tmul, hN, zero_tmul]

theorem main : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ r M N _ _ B _ _ T _ _ g h1 h2 h3
  constructor
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul n y =>
      obtain ⟨x, hx⟩ := h2 y
      refine ⟨n ⊗ₜ x, ?_⟩
      have h0 := tmul_eq_zero_of_mem_span (r 0) M h1 n _ hx
      rw [tmul_sub, sub_eq_zero] at h0
      rw [h0]
      simp
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
  · intro w hw k
    choose s hs using h2
    let I : Ideal T := Ideal.span {algebraMap R T (r 0) ^ M}
    let P : Submodule R B := (Ideal.span {algebraMap R B (r 0) ^ M}).restrictScalars R
    have key : ∀ x : B, g x ∈ I → r k • x ∈ P := fun x hx => h3 x hx k
    have hadd : ∀ y y' : T, r k • s (y + y') - (r k • s y + r k • s y') ∈ P := by
      intro y y'
      rw [← smul_add, ← smul_sub]
      apply key
      have e : g (s (y + y') - (s y + s y')) =
          (y - g (s y)) + (y' - g (s y')) - (y + y' - g (s (y + y'))) := by
        simp only [map_sub, map_add (f := _)]; ring
      rw [e]
      exact I.sub_mem (I.add_mem (hs y) (hs y')) (hs _)
    have hsmul : ∀ (c : R) (y : T), r k • s (c • y) - c • (r k • s y) ∈ P := by
      intro c y
      rw [smul_comm c, ← smul_sub]
      apply key
      have e : g (s (c • y) - c • s y) =
          algebraMap R T c * (y - g (s y)) - (c • y - g (s (c • y))) := by
        rw [map_sub, map_smul, mul_sub, ← Algebra.smul_def, ← Algebra.smul_def]; abel
      rw [e]
      exact I.sub_mem (I.mul_mem_left _ (hs y)) (hs _)
    let L : T →ₗ[R] B ⧸ P :=
      { toFun := fun y => P.mkQ (r k • s y)
        map_add' := fun y y' => by
          rw [← map_add (f := _)]
          exact (Submodule.Quotient.eq P).mpr (hadd y y')
        map_smul' := fun c y => by
          simp only [RingHom.id_apply]
          rw [← map_smul]
          exact (Submodule.Quotient.eq P).mpr (hsmul c y) }
    let F : (B ⧸ P) →ₗ[R] N →ₗ[R] N ⊗[R] B :=
      P.liftQ (TensorProduct.mk R N B).flip (by
        intro b hb
        rw [LinearMap.mem_ker]
        ext n
        exact tmul_eq_zero_of_mem_span (r 0) M h1 n b hb)
    let Φ : N ⊗[R] T →ₗ[R] N ⊗[R] B := TensorProduct.lift (F ∘ₗ L).flip
    have hΦ : ∀ (n : N) (y : T), Φ (n ⊗ₜ y) = n ⊗ₜ (r k • s y) := fun n y => by
      simp [Φ, F, L]
    have hcomp : ∀ v : N ⊗[R] B, Φ (g.toLinearMap.lTensor N v) = r k • v := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul n b =>
        rw [LinearMap.lTensor_tmul, hΦ, ← tmul_smul, ← sub_eq_zero, ← tmul_sub, ← smul_sub]
        apply tmul_eq_zero_of_mem_span (r 0) M h1 n
        apply key
        have e : g (s (g b) - b) = -(g b - g (s (g b))) := by
          simp only [map_sub]; ring
        have e' : (g.toLinearMap) b = g b := rfl
        rw [e', e]
        exact I.neg_mem (hs _)
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, smul_add]
    rw [← hcomp w, hw, map_zero]

end GlobalTheory.CompanionTheory.TensCompl
end

