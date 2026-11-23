module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SimLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem ext_form {x y : D.La} (h : ∀ b, D.EF x b = D.EF y b) : x = y :=
  D.unimod.1 (LinearMap.ext h)

theorem form_skew (x y : D.La) : D.EF x y = -D.EF y x := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

theorem exists_vec (φ : D.La → ℤ) (hφ : ∀ a b, φ (a + b) = φ a + φ b) : ∃ x, ∀ b, D.EF x b = φ b := by
  obtain ⟨x, hx⟩ := D.unimod.2 (AddMonoidHom.mk' φ hφ).toIntLinearMap
  exact ⟨x, fun b => by rw [hx]; rfl⟩

theorem exists_rep (B : D.La → D.La → ℤ) (h1 : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (h2 : ∀ a b b', B a (b + b') = B a b + B a b')
    (h3 : ∀ (c : 𝓞 E) a b, B (c • a) b = B a (H.bar c • b)) :
    ∃ u : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (u a) b = B a b := by
  choose u hu using fun a => exists_vec D (B a) (h2 a)
  refine ⟨⟨⟨u, fun a a' => ext_form D fun b => ?_⟩, fun c a => ext_form D fun b => ?_⟩, hu⟩
  · rw [map_add (f := _), LinearMap.add_apply, hu, hu, hu, h1]
  · simp only [RingHom.id_apply]
    rw [D.adj, hu, hu, h3]

theorem modN_of_dvd {n : ℕ} (hn : 0 < n) {x : D.La} (h : ∀ b, (n : ℤ) ∣ D.EF x b) : D.ModN n x := by
  choose φ hφ using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨y, hy⟩ := exists_vec D φ fun a b => by
    apply mul_left_cancel₀ hn'
    rw [← hφ, map_add (f := _), hφ, hφ, mul_add]
  refine ⟨y, ext_form D fun b => ?_⟩
  rw [map_nsmul, LinearMap.smul_apply, hy, hφ, nsmul_eq_mul]

theorem modN_of_dvd_modulus {n m : ℕ} (h : n ∣ m) {x : D.La} (hx : D.ModN m x) : D.ModN n x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hx
  exact ⟨k • b, mul_smul _ _ _⟩

theorem modN_trans {n : ℕ} {x y z : D.La} (h1 : D.ModN n (x - y)) (h2 : D.ModN n (y - z)) :
    D.ModN n (x - z) := by
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  exact ⟨b + c, by rw [smul_add, ← hb, ← hc]; abel⟩

def IsSimMod (n : ℕ) (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ) : Prop :=
  IsCoprime ν (n : ℤ) ∧ ∀ a b, (n : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b

theorem IsSimMod.of_dvd {n m : ℕ} (h : n ∣ m) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D m f ν) :
    IsSimMod D n f ν :=
  have h' : (n : ℤ) ∣ m := Int.natCast_dvd_natCast.mpr h
  ⟨hf.1.of_isCoprime_of_dvd_right h', fun a b => h'.trans (hf.2 a b)⟩

theorem step_sq {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ f', IsSimMod D (n * n) f' ν ∧ ∀ a, D.ModN n (f' a - f a) := by
  obtain ⟨hc, hB⟩ := hf
  have hc2 : IsCoprime ν ((n * n : ℕ) : ℤ) := by
    push_cast; exact hc.mul_right hc
  obtain ⟨κ, t, hκ⟩ := hc
  choose B hB using hB
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨u, hu⟩ := exists_rep D B
    (fun a a' b => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (fun a b b' => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add (f := _)]; ring)
    (fun c a b => by
      apply mul_left_cancel₀ hn'
      rw [← hB, ← hB, f.map_smul, f.map_smul, D.adj, D.adj])
  have hskew : ∀ a b, B a b = -B b a := fun a b => by
    apply mul_left_cancel₀ hn'
    rw [mul_neg, ← hB, ← hB, form_skew D (f a), form_skew D a]; ring
  have hsa : ∀ a b, D.EF a (u b) = D.EF (u a) b := fun a b => by
    rw [form_skew D a, hu, hu, hskew a b]
  set v : D.La →ₗ[𝓞 E] D.La := H.w0 • u with hv
  have hkey : ∀ a b, D.EF (v a) b + D.EF a (v b) = B a b := fun a b => by
    have h1 : D.EF a (v b) = D.EF ((1 - H.w0) • u a) b := by
      have hb : H.bar (1 - H.w0) = H.w0 := by
        rw [map_sub, map_one, HostModel.cmHost_bar_halfIntegerGenerator]; ring
      rw [← u.map_smul, ← hsa, D.adj, hb, hv, LinearMap.smul_apply]
    rw [h1, ← LinearMap.add_apply, ← map_add (f := _), hv, LinearMap.smul_apply, ← add_smul, ← hu]
    simp
  have hff : ∀ a b, D.EF (f a) (f b) = ν * D.EF a b + n * B a b := fun a b => by
    rw [← hB]; ring
  refine ⟨f - ((n : ℤ) * κ) • (f ∘ₗ v), ⟨hc2, fun a b => ?_⟩, fun a => ⟨-(κ • f (v a)), ?_⟩⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_zsmul,
      smul_eq_mul, hff]
    refine ⟨t * B a b - κ * (B (v a) b + B a (v b)) +
      κ * κ * (ν * D.EF (v a) (v b) + n * B (v a) (v b)), ?_⟩
    push_cast
    linear_combination (-(n : ℤ) * κ * ν) * hkey a b - (n : ℤ) * B a b * hκ
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [mul_smul, natCast_zsmul, smul_neg]; abel

theorem step_coprime {n r : ℕ} (hnr : IsCoprime (n : ℤ) (r : ℤ)) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ}
    (hf : IsSimMod D n f ν) :
    ∃ f' ν', IsSimMod D (n * r) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  obtain ⟨x, y, hxy⟩ := hnr
  obtain ⟨hc, hB⟩ := hf
  refine ⟨(y * r) • f + (x * n) • LinearMap.id, y * r * ν + x * n, ⟨?_, fun a b => ?_⟩,
    fun a => ⟨x • (a - f a), ?_⟩, ⟨x * (1 - ν), by linear_combination ν * hxy⟩⟩
  · push_cast
    refine IsCoprime.mul_right ?_ ?_
    · obtain ⟨κ, t, hκ⟩ := hc
      exact ⟨κ, t - κ * x * (1 - ν), by linear_combination hκ + κ * ν * hxy⟩
    · exact ⟨1, y * (1 - ν), by linear_combination hxy⟩
  · obtain ⟨B, hB⟩ := hB a b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add (f := _), map_zsmul,
      smul_eq_mul]
    refine ⟨y * B + x * y * (D.EF (f a) b + D.EF a (f b) - D.EF (f a) (f b) - D.EF a b), ?_⟩
    push_cast
    linear_combination (y * r) * hB + (y * r * D.EF (f a) (f b) + x * n * D.EF a b) * hxy
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have h : y * (r : ℤ) = 1 - n * x := by linear_combination hxy
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm x, sub_smul, smul_sub, one_smul]; abel

theorem step (m : ℕ) : 0 < m → ∀ (n : ℕ), 0 < n → ∀ (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), IsSimMod D n f ν →
    ∃ f' ν', IsSimMod D (n * m) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ n _ f ν hf
    exact ⟨f, ν, by simpa using hf, fun a => ⟨0, by simp⟩, by simp⟩
  | prime_mul p a hp ih =>
    intro hpa n hn f ν hf
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have h1 : ∃ f' ν', IsSimMod D (n * p) f' ν' ∧ (∀ a, D.ModN n (f' a - f a)) ∧ (n : ℤ) ∣ ν' - ν := by
      by_cases hpn : p ∣ n
      · obtain ⟨f', h1, h2⟩ := step_sq D hn hf
        exact ⟨f', ν, h1.of_dvd D (Nat.mul_dvd_mul_left n hpn), h2, by simp⟩
      · exact step_coprime D
          (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm) hf
    obtain ⟨f₁, ν₁, h1, h2, h3⟩ := h1
    obtain ⟨f₂, ν₂, h4, h5, h6⟩ := ih ha (n * p) (Nat.mul_pos hn hp.pos) f₁ ν₁ h1
    refine ⟨f₂, ν₂, by rwa [← Nat.mul_assoc], fun x =>
      modN_trans D (modN_of_dvd_modulus D (dvd_mul_right n p) (h5 x)) (h2 x), ?_⟩
    have h7 : (n : ℤ) ∣ ν₂ - ν₁ := (Int.natCast_dvd_natCast.mpr (dvd_mul_right n p)).trans h6
    simpa using dvd_add h7 h3

theorem exists_inv {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, ∀ a, D.ModN n (g (f a) - a) ∧ D.ModN n (f (g a) - a) := by
  obtain ⟨⟨κ, t, hκ⟩, hB⟩ := hf
  obtain ⟨u, hu⟩ := exists_rep D (fun a b => D.EF a (f b)) (fun a a' b => by simp)
    (fun a b b' => by simp) (fun c a b => by rw [f.map_smul, D.adj])
  set g : D.La →ₗ[𝓞 E] D.La := κ • u with hg
  have h1 : ∀ a, D.ModN n (g (f a) - a) := fun a => modN_of_dvd D hn fun b => by
    obtain ⟨B, hB⟩ := hB a b
    simp only [hg, LinearMap.smul_apply, map_sub, map_zsmul, LinearMap.sub_apply, smul_eq_mul, hu]
    exact ⟨κ * B - t * D.EF a b, by linear_combination κ * hB + D.EF a b * hκ⟩
  let S : Submodule (𝓞 E) D.La := LinearMap.range (n • (LinearMap.id : D.La →ₗ[𝓞 E] D.La))
  have hS : ∀ x, x ∈ S ↔ D.ModN n x := fun x =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hgS : S ≤ S.comap g := by
    rintro x hx
    obtain ⟨b, rfl⟩ := (hS x).mp hx
    exact (hS _).mpr ⟨g b, map_nsmul g n b⟩
  have := D.fin
  have hsurj : Function.Surjective (S.mapQ S g hgS) := by
    intro q
    obtain ⟨a, rfl⟩ := S.mkQ_surjective q
    exact ⟨S.mkQ (f a), (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 a))⟩
  have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  refine ⟨g, fun a => ⟨h1 a, (hS _).mp ((Submodule.Quotient.eq S).mp (hinj ?_))⟩⟩
  exact (Submodule.Quotient.eq S).mpr ((hS _).mpr (h1 (g a)))

end GlobalTheory.SimLift

namespace GlobalTheory

open SimLift

theorem exists_sim_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ)
    (f : D.La →ₗ[𝓞 E] D.La) (ν : ℤ), 0 < N → IsCoprime ν (N : ℤ) →
    (∀ a b, (N : ℤ) ∣ D.EF (f a) (f b) - ν * D.EF a b) →
    ∃ g : Sim D, (∀ a, D.ModN N (g.f N a - f a)) ∧ (N : ℤ) ∣ g.ν N - ν := by
  intro E _ _ _ H D N f ν hN hc hf
  let T : ℕ → Type := fun k =>
    {x : (D.La →ₗ[𝓞 E] D.La) × ℤ // IsSimMod D (N * k.factorial) x.1 x.2}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1),
      (∀ a, D.ModN (N * k.factorial) (y.1.1 a - x.1.1 a)) ∧ ((N * k.factorial : ℕ) : ℤ) ∣ y.1.2 - x.1.2 := by
    intro k x
    obtain ⟨f', ν', h1, h2⟩ := step D (k + 1) k.succ_pos _ (Nat.mul_pos hN k.factorial_pos) _ _ x.2
    refine ⟨⟨(f', ν'), ?_⟩, h2⟩
    rwa [Nat.factorial_succ, Nat.mul_comm (k + 1), ← Nat.mul_assoc]
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨(f, ν), by
    rw [Nat.factorial_zero, Nat.mul_one]; exact ⟨hc, hf⟩⟩ : T 0) nx k
  have hs : ∀ k j, k ≤ j → (∀ a, D.ModN (N * k.factorial) ((s j).1.1 a - (s k).1.1 a)) ∧
      ((N * k.factorial : ℕ) : ℤ) ∣ (s j).1.2 - (s k).1.2 := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact ⟨fun a => ⟨0, by simp⟩, by simp⟩
    | succ j hkj ih =>
      have hd : N * k.factorial ∣ N * j.factorial :=
        Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial hkj)
      obtain ⟨h1, h2⟩ := hnx j (s j)
      refine ⟨fun a => modN_trans D (modN_of_dvd_modulus D hd (h1 a)) (ih.1 a), ?_⟩
      have h3 := dvd_add ((Int.natCast_dvd_natCast.mpr hd).trans h2) ih.2
      rwa [sub_add_sub_cancel] at h3
  have hd : ∀ n, 0 < n → n ∣ N * n.factorial := fun n hn =>
    (Nat.dvd_factorial hn le_rfl).mul_left N
  refine ⟨⟨fun n => (s n).1.1, fun n => (s n).1.2, fun n m hn hm a => ?_, fun n hn => ?_,
    fun n hn => ?_⟩, fun a => ?_, ?_⟩
  · exact modN_of_dvd_modulus D (hd n hn) ((hs n _ (Nat.le_mul_of_pos_right n hm)).1 a)
  · exact exists_inv D hn ((s n).2.of_dvd D (hd n hn))
  · exact ((s n).2.of_dvd D (hd n hn)).2
  · exact modN_of_dvd_modulus D (dvd_mul_right N _) ((hs 0 N N.zero_le).1 a)
  · exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right N _)).trans (hs 0 N N.zero_le).2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

variable {S : Scheme.{0}}

def ClopenCond (T : Over S) (P : ∀ T' : Over S, (T' ⟶ T) → Prop) : Prop :=
  ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T), P T' h ↔ Set.range h.left ⊆ U

theorem ClopenCond.congr {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (e : ∀ T' h, P' T' h ↔ P T' h) : ClopenCond T P' := by
  obtain ⟨U, hU, H⟩ := h
  exact ⟨U, hU, fun T' h => (e T' h).trans (H T' h)⟩

theorem ClopenCond.and {T : Over S} {P P' : ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ClopenCond T P)
    (h' : ClopenCond T P') : ClopenCond T fun T' h => P T' h ∧ P' T' h := by
  obtain ⟨U, hU, H⟩ := h
  obtain ⟨U', hU', H'⟩ := h'
  refine ⟨U ⊓ U', hU.inter hU', fun T' h => ?_⟩
  beta_reduce
  rw [H, H', TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]

theorem ClopenCond.forall_finite {T : Over S} {J : Type} [Finite J] {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop}
    (h : ∀ i, ClopenCond T (P i)) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  choose U hU H using h
  refine ⟨⟨⋂ i, (U i : Set T.left), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, isClosed_iInter hU,
    fun T' h => ?_⟩
  simp only [H, TopologicalSpace.Opens.coe_mk, Set.subset_iInter_iff]

theorem ClopenCond.forall_of_finite {T : Over S} {J κ : Type} [Finite κ] (q : J → κ)
    {P : J → ∀ T' : Over S, (T' ⟶ T) → Prop} (h : ∀ i, ClopenCond T (P i))
    (hq : ∀ i j, q i = q j → ∀ T' h, P i T' h → P j T' h) : ClopenCond T fun T' h => ∀ i, P i T' h := by
  refine (ClopenCond.forall_finite (J := Set.range q) fun c => h c.2.choose).congr fun T' h => ?_
  exact ⟨fun H c => H _, fun H i => hq _ _ (⟨i, rfl⟩ : q i ∈ Set.range q).choose_spec T' h (H ⟨q i, i, rfl⟩)⟩

theorem exists_finite_mod (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    ∃ (κ : Type) (_ : Finite κ) (q : M → κ), ∀ a a', q a = q a' → ∃ c, a' = a + n • c := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let b := Module.Free.chooseBasis ℤ M
  refine ⟨Module.Free.ChooseBasisIndex ℤ M → ZMod n, inferInstance, fun a i => (b.repr a i : ZMod n),
    fun a a' h => ?_⟩
  have h1 : ∀ i, ∃ c : ℤ, b.repr a' i - b.repr a i = n * c := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h i)
  choose c hc using h1
  refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
  rw [map_add (f := _), map_nsmul, LinearEquiv.apply_symm_apply]
  simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  linarith [hc i]

theorem clopenCond_eq {T Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (u u' : T ⟶ Z) :
    ClopenCond T fun _ h => h ≫ u = h ≫ u' := by
  refine ⟨(FinEt.agreeι u u').opensRange, (FinEt.agreeι u u').isClosedEmbedding.isClosed_range, fun T' h => ?_⟩
  refine Iff.trans ?_ (FinEt.comp_eq_comp_iff_range u u' h.left)
  exact ⟨fun e => congrArg CommaMorphism.left e, fun e => Over.OverMorphism.ext e⟩

def RepTors (G : Over S) [GrpObj G] (n : ℕ) (La : Type) [AddCommGroup La] (Z : Over S) (et : La → (Z ⟶ G)) : Prop :=
  IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧ (∀ a, et a ^ n = 1) ∧
    ∀ (T : Over S) (et' : La → (T ⟶ G)), (∀ a c, et' (a + c) = et' a * et' c) → (∀ a, et' a ^ n = 1) →
      ∃! h : T ⟶ Z, ∀ a, h ≫ et a = et' a

theorem RepTors.ext {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S} {et : La → (Z ⟶ G)}
    (R : RepTors G n La Z et) {T : Over S} {u u' : T ⟶ Z} (h : ∀ a, u ≫ et a = u' ≫ et a) : u = u' :=
  (R.2.2.2.2 T (fun a => u' ≫ et a) (fun a c => by rw [R.2.2.1, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one])).unique h fun _ => rfl

theorem RepTors.clopenCond {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S}
    {et : La → (Z ⟶ G)} (R : RepTors G n La Z et) {T : Over S} (x y : La → (T ⟶ G))
    (hx : ∀ a c, x (a + c) = x a * x c) (hx' : ∀ a, x a ^ n = 1)
    (hy : ∀ a c, y (a + c) = y a * y c) (hy' : ∀ a, y a ^ n = 1) :
    ClopenCond T fun _ h => ∀ a, h ≫ x a = h ≫ y a := by
  obtain ⟨u, hu, -⟩ := R.2.2.2.2 T x hx hx'
  obtain ⟨u', hu', -⟩ := R.2.2.2.2 T y hy hy'
  have := R.1
  have := R.2.1
  refine (clopenCond_eq u u').congr fun T' h => ⟨fun H => R.ext fun a => ?_, fun H a => ?_⟩
  · rw [Category.assoc, Category.assoc, hu, hu', H]
  · rw [← hu, ← hu', ← Category.assoc, H, Category.assoc]

theorem exists_lift_geom {W Z : Scheme.{0}} (p : W ⟶ Z) [IsFinite p] {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z) (hz : Set.range z ⊆ Set.range p) : ∃ w : Sp k ⟶ W, w ≫ p = z := by
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  have h1 : pt ∈ Set.range (pullback.snd p z) := by
    rw [Scheme.Pullback.range_snd]
    exact hz ⟨pt, rfl⟩
  obtain ⟨y, -⟩ := h1
  have : Nonempty (pullback p z : Scheme) := ⟨y⟩
  have : IsAffine (pullback p z) := isAffine_of_isAffineHom (pullback.snd p z)
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := (pullback p z : Scheme))).exists_closed_singleton Set.univ_nonempty
  refine ⟨pointOfClosedPoint (pullback.snd p z) x hx ≫ pullback.fst p z, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem exists_image {W Z : Over S} [IsFinite W.hom] [Etale W.hom] [IsFinite Z.hom] [Etale Z.hom] (p : W ⟶ Z) :
    ∃ U : Z.left.Opens, IsClosed (U : Set Z.left) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
      (z : Over.mk x ⟶ Z), Set.range z.left ⊆ U ↔ ∃ w : Over.mk x ⟶ W, w ≫ p = z := by
  have := FinEt.isFinite_left p
  have := FinEt.etale_left p
  refine ⟨⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩, p.left.isClosedMap.isClosed_range,
    fun k _ _ x z => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_lift_geom p.left z.left h
    refine ⟨Over.homMk w ?_, Over.OverMorphism.ext hw⟩
    show w ≫ W.hom = x
    rw [← Over.w p, ← Category.assoc, hw]
    exact Over.w z
  · rintro ⟨w, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨w.left y, by simp⟩

theorem exists_sub {Z : Over S} [IsFinite Z.hom] [Etale Z.hom] (U : Z.left.Opens) (hU : IsClosed (U : Set Z.left)) :
    ∃ (V : Over S) (i : V ⟶ Z), IsFinite V.hom ∧ Etale V.hom ∧ Mono i ∧
      ∀ (T : Over S) (h : T ⟶ Z), Set.range h.left ⊆ U ↔ ∃ h' : T ⟶ V, h' ≫ i = h := by
  have hc : IsClosedImmersion U.ι := .of_isPreimmersion _ (by simpa using hU)
  refine ⟨Over.mk (U.ι ≫ Z.hom), Over.homMk U.ι rfl, inferInstanceAs (IsFinite (U.ι ≫ Z.hom)),
    inferInstanceAs (Etale (U.ι ≫ Z.hom)), ?_, fun T h => ?_⟩
  · have : Mono (Over.homMk U.ι rfl : Over.mk (U.ι ≫ Z.hom) ⟶ Z).left := inferInstanceAs (Mono U.ι)
    exact Over.mono_of_mono_left _
  · rw [FinEt.range_subset_iff_factors]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨Over.homMk t ?_, Over.OverMorphism.ext ht⟩
      show t ≫ U.ι ≫ Z.hom = T.hom
      rw [← Category.assoc, ht, Over.w h]
    · rintro ⟨t, ht⟩
      exact ⟨t.left, congrArg CommaMorphism.left ht⟩

theorem range_subset_of_geom {T Z : Over S} (h : T ⟶ Z) (U : Set Z.left)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ T), Set.range (y ≫ h).left ⊆ U) :
    Set.range h.left ⊆ U := by
  rintro _ ⟨t, rfl⟩
  obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T.left t
  obtain ⟨p, rfl⟩ : t ∈ Set.range a := by rw [ha]; rfl
  exact H k (a ≫ T.hom) (Over.homMk a rfl) ⟨p, by simp⟩

theorem finiteEtale_tensor (X Y : Over S) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsFinite (X ⊗ Y).hom ∧ Etale (X ⊗ Y).hom :=
  ⟨inferInstanceAs (IsFinite (pullback.fst X.hom Y.hom ≫ X.hom)),
    inferInstanceAs (Etale (pullback.fst X.hom Y.hom ≫ X.hom))⟩

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfIsPullbackOfSurjectiveOfFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem smooth_of_isPullback_of_surjective_of_flat :
    ∀ (X X' Y Y' : Scheme.{0}) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), IsPullback φ p p' π → Surjective π → Flat p' → LocallyOfFinitePresentation p' → Smooth p → Smooth p' := by
  intro X X' Y Y' π φ p p' h hπ hflat hlfp hsm

  refine Smooth.of_smooth_fiberToSpecResidueField p' fun y' => ?_

  obtain ⟨y, rfl⟩ := hπ.surj y'

  have hsq := (isPullback_fiberToSpecResidueField_of_isPullback h y).flip

  have hff : (π.residueFieldMap y).hom.FaithfullyFlat := by
    letI := (π.residueFieldMap y).hom.toAlgebra
    show Module.FaithfullyFlat _ _
    infer_instance
  obtain ⟨hF, hS⟩ := (flat_and_surjective_SpecMap_iff _).2 hff

  have hfib : Smooth (p.fiberToSpecResidueField y) :=
    inferInstanceAs (Smooth (pullback.snd p (X.fromSpecResidueField y)))

  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq ⟨⟨hS, hF⟩, inferInstance⟩ hfib

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem hermForm_self_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z : Fin g → ℂ) : (hermForm Hm z z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
    Pi.star_apply, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← h.apply j k, Complex.star_def]
  ring

theorem free_finite_finrank_of_discrete_span {La : Type} [AddCommGroup La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hd : DiscreteTopology Q.range)
    (hsp : Submodule.span ℝ (Set.range Q) = ⊤) :
    Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g := by
  set L : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    rw [hL, LinearMap.coe_range]
    exact hsp⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem unimodular_symplectic_coordinates_and_lattice_rank :
    (∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ), Function.Bijective EF → (∀ x, EF x x = 0) → Module.finrank ℤ La = 2 * g → ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La, ∀ a b, EF (bas a) (bas b) = omegaStd a b) ∧ ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧ ∀ x, EF x x = 0 := by
  refine ⟨fun La _ _ _ EF g hbij halt hrk => ?_,
    fun La _ EF g Q Hm ⟨hinj, hd, hsp, hH, _, hIm⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank (B := EF) halt hbij hrk
    have hf : IsSymplecticFamily EF (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i))
        (fun _ => 1) := hb
    classical
    refine ⟨b.equivFun.symm, fun x y => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, map_add (f := _), LinearMap.add_apply,
      map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [hf.left_left, hf.right_right, hf.left_right, hf.right_left halt, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, _root_.mul_one, mul_neg,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, omegaStd]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_discrete_span Q hinj hd hsp
    exact ⟨h1, h2, h3, fun x => by
      have e : ((EF x x : ℤ) : ℝ) = 0 := by rw [← hIm x x]; exact hermForm_self_im_eq_zero hH _
      exact_mod_cast e⟩

end GlobalTheory
end

