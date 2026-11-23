module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureZmodTorsorGenericFibreData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

namespace CupSpec

variable {R : Type} [CommRing R]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g :=
  ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x

section Cup
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc}

def awF {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U) : Sec (K.X w) U :=
  ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev a p _ rfl U (x.sub 0 p (by omega))) (ev b (N - p) _ rfl U (x.sub p (N - p) (by omega)))

theorem awF_res {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) :
    Sec.res g (awF μ hk a b N w h U x) = awF μ hk a b N w h V (x.res g) := by
  unfold awF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Sec.res, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, sub_res, sub_res, ← ev_res, ← ev_res, ← μ.nat]

theorem isAW_exists {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) :
    ∃ c, μ.IsAW hk a b c := by
  obtain ⟨c, hc⟩ := ev_exists (awF μ hk a b) (fun N w h V U g x => awF_res μ hk a b N w h g x)
  exact ⟨c, hc⟩

theorem isAW_unique {n m k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ev_ext c c' fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem isAW_add_left {n m k : ℤ} (hk : n + m = k) {a a' : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a' b c') : μ.IsAW hk (a + a') b (c + c') := by
  intro N w hw U x
  rw [ev_add, h N w hw U x, h' N w hw U x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem isAW_add_right {n m k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b b' : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b' c') : μ.IsAW hk a (b + b') (c + c') := by
  intro N w hw U x
  rw [ev_add, h N w hw U x, h' N w hw U x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_add, map_add (f := _), smul_add]

theorem isAW_zero_left {n m k : ℤ} (hk : n + m = k) (b : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 b 0 := by
  intro N w hw U x
  simp [ev_zero]

theorem isAW_zero_right {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a 0 0 := by
  intro N w hw U x
  simp [ev_zero]

theorem aw_cocycle {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (c : Cochain ((chains R).obj E) K k) (hc : μ.IsAW hk α.1 β.1 c) : δ k (k + 1) c = 0 := by
  have h₁ : μ.IsAW (by omega : (n + 1) + m = k + 1) (δ n (n + 1) α.1) β.1 0 := by
    rw [Cocycle.δ_eq_zero]; exact isAW_zero_left μ _ _
  have h₂ : μ.IsAW (by omega : n + (m + 1) = k + 1) α.1 (δ m (m + 1) β.1) 0 := by
    rw [Cocycle.δ_eq_zero]; exact isAW_zero_right μ _ _
  rw [aw_leibniz μ rfl rfl rfl hc h₁ h₂]
  simp

def awc {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Cocycle.mk (isAW_exists μ hk α.1 β.1).choose (k + 1) rfl (aw_cocycle μ hk α β _ (isAW_exists μ hk α.1 β.1).choose_spec)

theorem awc_spec {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (awc μ hk α β).1 := (isAW_exists μ hk α.1 β.1).choose_spec

theorem awc_eq {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : awc μ hk α β = γ :=
  Cocycle.ext (isAW_unique μ hk (awc_spec μ hk α β) h)

def cupL {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) :
    CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun β => CohomologyClass.mk (awc μ hk α β)) (fun β β' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact awc_eq μ hk _ _ _ (isAW_add_right μ hk (awc_spec μ hk α β) (awc_spec μ hk α β'))))
    (by
      rintro ⟨b, hb⟩ ⟨m', hm', b', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨c₀, hc₀⟩ := isAW_exists μ (rfl : n + m' = n + m') α.1 b'
      have h₁ : μ.IsAW (by omega : (n + 1) + m' = k) (δ n (n + 1) α.1) b' 0 := by
        rw [Cocycle.δ_eq_zero]; exact isAW_zero_left μ _ _
      have hL := aw_leibniz μ rfl hm' (by omega) hc₀ h₁ (awc_spec μ hk α ⟨_, hb⟩)
      refine ⟨n + m', by omega, n.negOnePow • c₀, ?_⟩
      rw [δ_units_smul, hL, zero_add, smul_smul, Int.units_mul_self, one_smul])

theorem cupL_mk {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    cupL μ hk α (CohomologyClass.mk β) = CohomologyClass.mk (awc μ hk α β) := rfl

def cupMap {n m k : ℤ} (hk : n + m = k) :
    CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => cupL μ hk α) (fun α α' => by
      ext y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      rw [AddMonoidHom.add_apply, cupL_mk, cupL_mk, cupL_mk, ← CohomologyClass.mk_add]; congr 1
      exact awc_eq μ hk _ _ _ (isAW_add_left μ hk (awc_spec μ hk α β) (awc_spec μ hk α' β))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      ext y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨c₀, hc₀⟩ := isAW_exists μ (rfl : n' + m = n' + m) a' β.1
      have h₂ : μ.IsAW (by omega : n' + (m + 1) = k) a' (δ m (m + 1) β.1) 0 := by
        rw [Cocycle.δ_eq_zero]; exact isAW_zero_right μ _ _
      have hL := aw_leibniz μ hn' rfl (by omega) hc₀ (awc_spec μ hk ⟨_, ha⟩ β) h₂
      refine ⟨n' + m, by omega, c₀, ?_⟩
      rw [hL, smul_zero, add_zero])

end Cup

section Op
variable {S : Type} [CommRing S] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) {E : Spc} {n : ℤ}

theorem image_cochain_exists (a : Cochain ((chains S).obj E) I n) : ∃ b, ρ.IsImage a b :=
  ev_exists (fun p s h U x => ρ.app U s (ev a p s h U x)) (fun p s h V U g x => by rw [ρ.nat, ev_res])

theorem image_unique {a : Cochain ((chains S).obj E) I n} {b b' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) (h' : ρ.IsImage a b') : b = b' :=
  ev_ext b b' fun p s hs U x => (h p s hs U x).trans (h' p s hs U x).symm

theorem image_add {a a' : Cochain ((chains S).obj E) I n} {b b' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) (h' : ρ.IsImage a' b') : ρ.IsImage (a + a') (b + b') := fun p s hs U x => by
  rw [ev_add, ev_add, map_add (f := _), h p s hs, h' p s hs]

theorem image_zero : ρ.IsImage (0 : Cochain ((chains S).obj E) I n) 0 := fun p s hs U x => by
  rw [ev_zero, ev_zero, map_zero]

theorem image_δ {m : ℤ} (hm : n + 1 = m) {a : Cochain ((chains S).obj E) I n} {b : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) : ρ.IsImage (δ n m a) (δ n m b) := by
  intro p t ht U x
  cases p with
  | zero => rw [ev_δ_zero hm b U _ t rfl, ev_δ_zero hm a U _ t rfl, h, ρ.comm]
  | succ p =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ev_δ_succ hm b U p _ t rfl, ev_δ_succ hm a U p _ t rfl, h, ρ.comm, map_add (f := _), sg_smul, sg_smul, map_zsmul, map_sum]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, h]

theorem image_pull {E' : Spc} (f : E' ⟶ E) {a : Cochain ((chains S).obj E) I n} {b : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) : ρ.IsImage ((Cochain.ofHom ((chains S).map f)).comp a (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp b (zero_add n)) := fun p s hs U x => by
  rw [ev_pull, ev_pull, h]

def imgc (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  Cocycle.mk (image_cochain_exists ρ α.1).choose (n + 1) rfl (by
    have h := image_δ ρ rfl (image_cochain_exists ρ α.1).choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact image_unique ρ h (image_zero ρ))

theorem imgc_spec (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (imgc ρ α).1 :=
  (image_cochain_exists ρ α.1).choose_spec

theorem imgc_eq (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n) (h : ρ.IsImage α.1 β.1) :
    imgc ρ α = β := Cocycle.ext (image_unique ρ (imgc_spec ρ α) h)

def opMap : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc ρ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq ρ _ _ (image_add ρ (imgc_spec ρ α) (imgc_spec ρ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb⟩ := image_cochain_exists ρ a'
      exact ⟨n', hn', b, image_unique ρ (image_δ ρ hn' hb) (imgc_spec ρ ⟨_, ha⟩)⟩)
  nat f n x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (imgc_eq ρ (zcomp (Cocycle.ofHom ((chains S).map f)) x (zero_add n))
      (zcomp (Cocycle.ofHom ((chains R).map f)) (imgc ρ x) (zero_add n)) (image_pull ρ f (imgc_spec ρ x))).symm

end Op

end CupSpec

open CupSpec

theorem Pair.cup_spec {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k) :
    μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro h
  have hP : ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
      CohomologyClass ((chains R).obj E) K k, ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k),
        μ.IsAW hk α.1 β.1 γ.1 → c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    ⟨cupMap μ hk, fun α β γ h => by
      change CohomologyClass.mk (awc μ hk α β) = _
      rw [awc_eq μ hk α β γ h]⟩
  exact pick_spec hP α β γ h

theorem Pair.aw_exists {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) : ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 :=
  ⟨awc μ hk α β, awc_spec μ hk α β⟩

theorem SemiMap.op_spec {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
    (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n) :
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) →
    ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : NatOp I J => ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n)
    (β : Cocycle ((chains R).obj E) J n),
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U),
      ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) → c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap ρ, fun _ _ α β h => congrArg CohomologyClass.mk (imgc_eq ρ α β h)⟩ E n α β

theorem SemiMap.image_exists {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
    (α : Cocycle ((chains S).obj E) I n) : ∃ β : Cocycle ((chains R).obj E) J n,
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x) :=
  ⟨imgc ρ α, imgc_spec ρ α⟩

theorem cup_op_spec :
    (∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      (∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ γ : Cocycle ((chains R).obj E) K k,
        μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ) ∧
    ∀ {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
      (α : Cocycle ((chains S).obj E) I n),
      (∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ β : Cocycle ((chains R).obj E) J n,
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  ⟨fun μ E _ _ _ hk α β => ⟨μ.aw_exists E hk α β, μ.cup_spec E hk α β⟩,
    fun ρ E n α => ⟨ρ.image_exists E n α, ρ.op_spec E n α⟩⟩

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureZmodTorsorGenericFibreDataStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_zmodTorsor_genericFibre_data : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [Nontrivial R] [Module.Flat A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    (∀ f : GlobalTheory.LocAcyc.GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r = f) →
    ∀ (q : ℕ) [NeZero q] (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] D)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) D q act →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∃ (act' : Multiplicative (ZMod q) →* (GlobalTheory.KeyOriginNoeth.closure A R D ≃ₐ[R] GlobalTheory.KeyOriginNoeth.closure A R D))
      (T : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] R),
      (∀ c, algebraMap R _ (T c) = ∑ g, act' g c) ∧
      (∃ a : A, a ≠ 0 ∧ ∃ (n : ℕ) (x y : Fin n → GlobalTheory.KeyOriginNoeth.closure A R D),
        ∀ g, ∑ i, x i * act' g (y i) = if g = 1 then algebraMap R _ (algebraMap A R a) else 0) ∧
      GlobalTheory.GoodEtale.TorsionFreeOver A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Algebra.IsIntegral R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Nontrivial (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.ClosureData.closureData) | (exact GlobalTheory.ClosureData.closureData) | (intros; apply GlobalTheory.ClosureData.closureData  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwiner
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma lam_idx_sq_eq_idx_of_fixed_ne_zero (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (lam : ℕ →* ℂ) (hlam : _root_.GlobalTheory.FinWeil.GoodNorm σ lam) {A A' : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (hA' : _root_.GlobalTheory.FinWeil.SelfDual γ A')
    (hidx : _root_.GlobalTheory.FinWeil.idx A A' ≠ 0) {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he0 : e ≠ 0) :
    lam (_root_.GlobalTheory.FinWeil.idx A A') ^ 2 = _root_.GlobalTheory.FinWeil.idx A A' := by
  have hAA := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A A hA e he Unit (fun _ => 0) (fun _ => zero_mem A)
    (fun b hb => ⟨(), by simpa using hb, fun _ _ => rfl⟩)
  have hcomp := _root_.GlobalTheory.FinWeil.normOp_comp hW lam hlam A A' A hA hA' hA hidx
    (by rw [hAA.2]; simp) e he
  obtain ⟨hsym, hback⟩ := _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul hW A A' hA hA' hidx
  have hlin : ∀ (c : ℂ) (v : M),
      _root_.GlobalTheory.FinWeil.sumOp W A' A (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A' A v := by
    intro c v
    unfold _root_.GlobalTheory.FinWeil.sumOp
    simp only [map_smul]
    rw [smul_finsum]
  unfold _root_.GlobalTheory.FinWeil.normOp at hcomp
  rw [hAA.1, hAA.2, hsym, hlin, hback e he] at hcomp
  simp only [Fintype.card_unit, map_one, inv_one, one_smul, Finset.univ_unique,
    Finset.sum_singleton, hW.zero, smul_smul] at hcomp
  have hc0 : lam (_root_.GlobalTheory.FinWeil.idx A A') ≠ 0 := hlam.1 _ hidx
  have hz : ((lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ * (lam (_root_.GlobalTheory.FinWeil.idx A A'))⁻¹ *
      (_root_.GlobalTheory.FinWeil.idx A A' : ℂ) - 1) • e = 0 := by
    rw [sub_smul, one_smul, mul_assoc, hcomp, sub_self]
  have h1 := (smul_eq_zero.1 hz).resolve_right he0
  field_simp at h1
  linear_combination -h1

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma mul_conj_eq_natCast_of_sq_eq (c : ℂ) (n : ℕ) (h : c ^ 2 = n) :
    c * starRingEnd ℂ c = n := by
  have hn : ‖c‖ ^ 2 = n := by rw [← norm_pow, h, Complex.norm_natCast]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  push_cast
  rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_vacuum_eq_zero
    (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x u v, B (W x u) (W x v) = B u v) {e e' : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (he' : _root_.GlobalTheory.FinWeil.Fixes W A e') {z : X} (hz : z ∉ A) : B (W z e) e' = 0 := by
  obtain ⟨a, ha, hza⟩ : ∃ a ∈ A, γ z a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hz ((hA z).2 h)
  have haz : γ a z ≠ 1 := fun h => hza (hW.swap_eq_one h)
  have key := hB a (W z e) e'
  rw [hW.comm, he a ha, he' a ha, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at key
  have : (γ a z - 1) * B (W z e) e' = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 haz)

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForm_translate_pair_eq (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (hB : ∀ x u v, B (W x u) (W x v) = B u v) (x y : X) (e e' : M) :
    B (W x e) (W y e') = γ (w • -y) x * (starRingEnd ℂ) (γ (w • -y) y) * B (W (-y + x) e) e' := by
  rw [← hB (-y) (W x e) (W y e'), hW.comp, hW.neg_comp]
  simp
  ring

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
  {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} in
private lemma invariantForms_eq_of_eq_on_vacua (hW : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤)
    (B₁ B₂ : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (h₁ : ∀ x u v, B₁ (W x u) (W x v) = B₁ u v)
    (h₂ : ∀ x u v, B₂ (W x u) (W x v) = B₂ u v)
    (hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ e e' = B₂ e e')
    (u v : M) : B₁ u v = B₂ u v := by
  have htr : ∀ z e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B₁ (W z e) e' = B₂ (W z e) e' := by
    intro z e e' he he'
    by_cases hz : z ∈ A
    · rw [he z hz]
      exact hvac e e' he he'
    · rw [invariantForm_translate_vacuum_eq_zero hW hA B₁ h₁ he he' hz,
        invariantForm_translate_vacuum_eq_zero hW hA B₂ h₂ he he' hz]
  have hS : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e},
      ∀ t ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s t = B₂ s t := by
    rintro s ⟨x, e, he, rfl⟩ t ⟨y, e', he', rfl⟩
    rw [invariantForm_translate_pair_eq hW B₁ h₁, invariantForm_translate_pair_eq hW B₂ h₂,
      htr _ e e' he he']
  have hleft : ∀ s ∈ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e}, B₁ s = B₂ s :=
    fun s hs => LinearMap.ext_on hspan (fun t ht => hS s hs t ht)
  have hflip : B₁.flip v = B₂.flip v :=
    LinearMap.ext_on hspan (fun s hs => by simp [hleft s hs])
  simpa using LinearMap.congr_fun hflip u


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.invForm_intertwiner : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, _root_.GlobalTheory.FinWeil.GoodNorm σ lam →
    ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    Submodule.span ℂ {m : M | ∃ x e, _root_.GlobalTheory.FinWeil.Fixes W A e ∧ m = W x e} = ⊤ →
    ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → _root_.GlobalTheory.FinWeil.SelfDual γ (A.map φ) →
    _root_.GlobalTheory.FinWeil.idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) →
    (∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map φ) e) →
    ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) →
    ∀ u v, B (T u) (T v) = B u v := by
  intro R X M _ _ _ _ _ σ w γ W hW _ lam hlam A hA hspan φ _ hA' hidx T hT hTe B hB u v
  obtain ⟨n, f, hfB, hfu⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map φ) hidx
  have hsum := fun e (he : _root_.GlobalTheory.FinWeil.Fixes W A e) =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A (A.map φ) hA' e he (Fin n) f hfB hfu
  have hvac : ∀ e e', _root_.GlobalTheory.FinWeil.Fixes W A e → _root_.GlobalTheory.FinWeil.Fixes W A e' →
      B (T e) (T e') = B e e' := by
    intro e e' he he'
    by_cases he0 : e = 0
    · subst he0
      simp
    have hn : _root_.GlobalTheory.FinWeil.idx A (A.map φ) = n := by simpa using (hsum e he).2
    have hc2 := lam_idx_sq_eq_idx_of_fixed_ne_zero hW lam hlam hA hA' hidx he he0
    rw [hn] at hc2
    have hcn := mul_conj_eq_natCast_of_sq_eq _ _ hc2
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hn ▸ hidx)
    have hT' : ∀ e, _root_.GlobalTheory.FinWeil.Fixes W A e → T e = (lam n)⁻¹ • ∑ i, W (f i) e := by
      intro e he
      rw [hTe e he]
      unfold _root_.GlobalTheory.FinWeil.normOp
      rw [hn, (hsum e he).1]
    have hterm : ∀ i j, B (W (f i) e) (W (f j) e') = if i = j then B e e' else 0 := by
      intro i j
      rw [← hB (-f j), hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB i),
        hW.comp_of_mem hA' (neg_mem (hfB j)) (hfB j), neg_add_cancel,
        hW.zero]
      split_ifs with hij
      · subst hij
        rw [neg_add_cancel, hW.zero]
      · apply invariantForm_translate_vacuum_eq_zero hW hA B hB he he'
        intro hmem
        apply hij
        obtain ⟨k, -, hk⟩ := hfu (f i) (hfB i)
        rw [hk i (by simp), hk j (by show f i - f j ∈ A; rwa [sub_eq_neg_add])]
    rw [hT' e he, hT' e' he']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_sum, LinearMap.sum_apply,
      smul_eq_mul, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, map_inv₀]
    have hinv : (lam n)⁻¹ * (starRingEnd ℂ (lam n))⁻¹ * n = 1 := by
      rw [← mul_inv, hcn, inv_mul_cancel₀ hn0]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linear_combination B e e' * hinv
  have key := invariantForms_eq_of_eq_on_vacua hW hA hspan ((B.comp T).compl₂ T) B
    (fun x u v => by simp [hT, hB]) hB (fun e e' he he' => by simpa using hvac e e' he he') u v
  simpa using key

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f →
      ConnectedSpace X → IrreducibleSpace X := by
  intro k _ X f hf hc
  haveI := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace f
  infer_instance

end GlobalTheory
end

