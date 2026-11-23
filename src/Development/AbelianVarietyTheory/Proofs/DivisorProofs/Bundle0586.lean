module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPPowerLevelFromPrimesAboveP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.LevCrt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {Q : Type} [CommGroup Q]

theorem mulle1 {A : Type} [CommRing A] (I J : Ideal A) : I * J ≤ I := Ideal.mul_le_inf.trans inf_le_left

theorem mulle2 {A : Type} [CommRing A] (I J : Ideal A) : I * J ≤ J := Ideal.mul_le_inf.trans inf_le_right

def iSub (D : Datum p) (I : Ideal (𝓞 D.F)) : Submodule D.O D.La :=
  Submodule.span D.O {z | ∃ c ∈ I, ∃ z' : D.La, z = algebraMap (𝓞 D.F) D.O c • z'}

theorem smul_mem_iSub {I : Ideal (𝓞 D.F)} {c : 𝓞 D.F} (hc : c ∈ I) (z : D.La) :
    algebraMap (𝓞 D.F) D.O c • z ∈ iSub D I :=
  Submodule.subset_span ⟨c, hc, z, rfl⟩

theorem iSub_mono {I J : Ideal (𝓞 D.F)} (h : I ≤ J) : iSub D I ≤ iSub D J :=
  Submodule.span_mono (by rintro _ ⟨c, hc, z, rfl⟩; exact ⟨c, h hc, z, rfl⟩)

theorem smul_mem_iSub_mul {I J : Ideal (𝓞 D.F)} {a : 𝓞 D.F} (ha : a ∈ I) {y : D.La} (hy : y ∈ iSub D J) :
    algebraMap (𝓞 D.F) D.O a • y ∈ iSub D (I * J) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, z, rfl⟩ := hx
    rw [smul_smul, ← map_mul]
    exact smul_mem_iSub (Ideal.mul_mem_mul ha hc) z
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [smul_smul, Algebra.commutes, ← smul_smul]
    exact Submodule.smul_mem _ _ hx

theorem mem_iSub_span_nat (n : ℕ) (x : D.La) :
    x ∈ iSub D (Ideal.span {(n : 𝓞 D.F)}) ↔ ∃ y, x = n • y := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, z, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc
      exact ⟨algebraMap (𝓞 D.F) D.O d • z, by
        rw [map_mul, map_natCast, ← smul_smul, Nat.cast_smul_eq_nsmul]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [smul_add]⟩
    | smul o x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨o • a, by rw [smul_comm]⟩
  · rintro ⟨y, rfl⟩
    have := smul_mem_iSub (D := D) (Ideal.mem_span_singleton_self (n : 𝓞 D.F)) y
    rwa [map_natCast, Nat.cast_smul_eq_nsmul] at this

def IsIdealLev (D : Datum p) (act : D.O → Q → Q) (I : Ideal (𝓞 D.F)) (f : D.La → Q) : Prop :=
  (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ x ∈ iSub D I) ∧
    ∀ g, (∀ c ∈ I, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, f y = g

theorem lev_top (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) : IsIdealLev D act ⊤ (fun _ => 1) := by
  refine ⟨fun _ _ => by simp, fun c _ => ?_, fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
  · exact Eq.symm (by simpa using hm c 1 1)
  · have := smul_mem_iSub (D := D) (I := ⊤) (c := 1) trivial x
    rw [map_one, one_smul] at this
    simpa using this
  · have := hg 1 trivial
    rw [map_one, h1] at this
    exact this.symm

theorem lev_mul (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) (hc : ∀ b c a, act (b * c) a = act b (act c a))
    (hadd : ∀ b c a, act (b + c) a = act b a * act c a) {I J : Ideal (𝓞 D.F)} (hIJ : I ⊔ J = ⊤)
    {f g : D.La → Q} (hf : IsIdealLev D act I f) (hg : IsIdealLev D act J g) :
    IsIdealLev D act (I * J) (fun x => f x * g x) := by
  obtain ⟨fa, fs, fk, fo⟩ := hf
  obtain ⟨ga, gs, gk, go⟩ := hg
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hIJ)
  have hone : ∀ c, act c 1 = 1 := fun c => by simpa using hm c 1 1
  have hsplit : ∀ u, act (algebraMap (𝓞 D.F) D.O a) u * act (algebraMap (𝓞 D.F) D.O b) u = u := fun u => by
    rw [← hadd, ← map_add (f := _), hab, map_one, h1]
  have fI : ∀ c ∈ I, ∀ x, act (algebraMap (𝓞 D.F) D.O c) (f x) = 1 := fun c hc x => by
    rw [← fs]; exact (fk _).2 (smul_mem_iSub hc x)
  have gJ : ∀ c ∈ J, ∀ x, act (algebraMap (𝓞 D.F) D.O c) (g x) = 1 := fun c hc x => by
    rw [← gs]; exact (gk _).2 (smul_mem_iSub hc x)
  refine ⟨fun x y => ?_, fun c x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun u hu => ?_⟩
  · simp only [fa, ga]; exact mul_mul_mul_comm _ _ _ _
  · simp only [fs, gs, hm]
  · have hx' : f x * g x = 1 := hx
    have e1 : f x = 1 := by
      have h := congrArg (act (algebraMap (𝓞 D.F) D.O b)) hx'
      rw [hm, gJ b hb, _root_.mul_one, hone] at h
      rw [← hsplit (f x), fI a ha, h, _root_.mul_one]
    have e2 : g x = 1 := by rwa [e1, _root_.one_mul] at hx'
    have hxx : x = algebraMap (𝓞 D.F) D.O a • x + algebraMap (𝓞 D.F) D.O b • x := by
      rw [← add_smul, ← map_add (f := _), hab, map_one, one_smul]
    rw [hxx]
    refine Submodule.add_mem _ (smul_mem_iSub_mul ha ((gk x).1 e2)) ?_
    rw [_root_.mul_comm I J]
    exact smul_mem_iSub_mul hb ((fk x).1 e1)
  · show f x * g x = 1
    have l1 : I * J ≤ I := mulle1 I J
    have l2 : I * J ≤ J := mulle2 I J
    rw [(fk x).2 (iSub_mono l1 hx), (gk x).2 (iSub_mono l2 hx), _root_.mul_one]
  · have k1 : ∀ c ∈ I, ∀ d ∈ J, act (algebraMap (𝓞 D.F) D.O c) (act (algebraMap (𝓞 D.F) D.O d) u) = 1 :=
      fun c hc' d hd => by rw [← hc, ← map_mul]; exact hu _ (Ideal.mul_mem_mul hc' hd)
    have k2 : ∀ c ∈ I, ∀ d ∈ J, act (algebraMap (𝓞 D.F) D.O d) (act (algebraMap (𝓞 D.F) D.O c) u) = 1 :=
      fun c hc' d hd => by rw [← hc, ← map_mul, _root_.mul_comm]; exact hu _ (Ideal.mul_mem_mul hc' hd)
    obtain ⟨z, hz⟩ := fo (act (algebraMap (𝓞 D.F) D.O b) u) fun c hc' => k1 c hc' b hb
    obtain ⟨y, hy⟩ := go (act (algebraMap (𝓞 D.F) D.O a) u) fun d hd => k2 a ha d hd
    refine ⟨algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b • z, ?_⟩
    show f _ * g _ = u
    rw [fa, ga, fs, fs, gs, gs, fI a ha, gJ b hb, _root_.one_mul, _root_.mul_one, hz, hy]
    have s1 := hsplit (act (algebraMap (𝓞 D.F) D.O a) u)
    have s2 := hsplit (act (algebraMap (𝓞 D.F) D.O b) u)
    rw [k2 a ha b hb, _root_.mul_one] at s1
    rw [k1 a ha b hb, _root_.one_mul] at s2
    rw [s1, s2, _root_.mul_comm, hsplit]

theorem exists_lev_of_pow_mem (act : D.O → Q → Q) (hm : ∀ c a b, act c (a * b) = act c a * act c b)
    (h1 : ∀ a, act 1 a = a) (hc : ∀ b c a, act (b * c) a = act b (act c a))
    (hadd : ∀ b c a, act (b + c) a = act b a * act c a)
    (H : ∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l, IsIdealLev D act (w ^ r) l)
    (r : ℕ) (I : Ideal (𝓞 D.F)) : (p : 𝓞 D.F) ^ r ∈ I → ∃ l, IsIdealLev D act I l := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 =>
    intro h
    have h0 : (p : 𝓞 D.F) ^ r = 0 := by simpa using h
    exact absurd (pow_eq_zero_iff'.1 h0).1 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  | h1 hu =>
    intro _
    rw [Ideal.isUnit_iff.1 hu]
    exact ⟨_, lev_top act hm h1⟩
  | @hpr q i hq =>
    intro h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact ⟨_, lev_top act hm h1⟩
    · have hp : q.IsPrime := Ideal.isPrime_of_prime hq
      exact H q i (hp.isMaximal hq.ne_zero) (hp.mem_of_pow_mem r (Ideal.pow_le_self hi.ne' h))
  | @hcp x y hxy hx hy =>
    intro h
    obtain ⟨f, hf⟩ := hx (mulle1 x y h)
    obtain ⟨g, hg⟩ := hy (mulle2 x y h)
    have : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact ⟨_, lev_mul act hm h1 hc hadd this hf hg⟩

theorem exists_pLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Q : Type) [CommGroup Q] (act : D.O → Q → Q), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ a, act 1 a = a) → (∀ b c a, act (b * c) a = act b (act c a)) → (∀ b c a, act (b + c) a = act b a * act c a) → (∀ (w : Ideal (𝓞 D.F)) (r : ℕ), w.IsMaximal → (p : 𝓞 D.F) ∈ w → ∃ l : D.La → Q, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = act c (l x)) ∧ (∀ x, l x = 1 ↔ x ∈ wSub D w r) ∧ ∀ g, (∀ c ∈ w ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g) → ∀ r : ℕ, ∃ f : D.La → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g) := by
  intro p _ D Q _ act hm h1 hc hadd H r
  obtain ⟨f, fa, fs, fk, fo⟩ := exists_lev_of_pow_mem act hm h1 hc hadd H r
    (Ideal.span {((p ^ r : ℕ) : 𝓞 D.F)}) (by
      rw [Nat.cast_pow]; exact Ideal.mem_span_singleton_self _)
  have hone : ∀ c, act c 1 = 1 := fun c => by simpa using hm c 1 1
  have hnat : ∀ (n : ℕ) a, act (n : D.O) a = a ^ n := fun n a => by
    induction n with
    | zero => simpa using hadd 0 0 a
    | succ n ih => rw [Nat.cast_succ, hadd, ih, h1, pow_succ]
  refine ⟨f, fa, fs, fun x => (fk x).trans (mem_iSub_span_nat _ x), fun g => ⟨fun hg => fo g ?_, ?_⟩⟩
  · intro c hc'
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.1 hc'
    rw [_root_.mul_comm, map_mul, hc, map_natCast, hnat, hg, hone]
  · rintro ⟨x, rfl⟩
    rw [← hnat, ← fs, Nat.cast_smul_eq_nsmul]
    exact (fk _).2 ((mem_iSub_span_nat _ _).2 ⟨x, rfl⟩)

end GlobalTheory.UPel.HT.EtLev.LevCrt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectPartAlgHomFiniteAlgebra
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem exists_perfectPart_algHom : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
    ∃ π : A →ₐ[k] A, ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) := by
  intro p _ k _ _ _ A _ _ _
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨AlgHom.id k A, fun a => ⟨1, Subsingleton.elim _ _⟩, fun a => ⟨a, Subsingleton.elim _ _⟩⟩
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical A
  set N := nilradical A with hNdef
  set q := p ^ (n + 1) with hqdef
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hq : ∀ x : A, x ∈ N → x ^ q = 0 := by
    intro x hx
    have h1 : x ^ n ∈ N ^ n := Ideal.pow_mem_pow hx n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at h1
    have hle : n ≤ q := by
      have := Nat.lt_pow_self (n := n + 1) hp1
      omega
    rw [← Nat.sub_add_cancel hle, pow_add, h1, mul_zero]
  haveI : Module.Finite k (A ⧸ N) := Module.Finite.trans A (A ⧸ N)
  haveI : IsReduced (A ⧸ N) := (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)
  have hroot : ∀ m : ℕ, ∀ a : A ⧸ N, ∃ b, a = b ^ p ^ m := by
    intro m
    induction m with
    | zero => intro a; exact ⟨a, by simp⟩
    | succ m ih =>
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.exists_pow_char_eq_of_isReduced_finite p k (A ⧸ N) b
      exact ⟨c, by rw [hb, hc, ← pow_mul, ← pow_succ']⟩
  have hlift : ∀ a : A, ∃ b : A, a - b ^ q ∈ N := by
    intro a
    obtain ⟨c, hc⟩ := hroot (n + 1) (Ideal.Quotient.mk N a)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, ?_⟩
    rw [← Ideal.Quotient.eq, map_pow]
    exact hc
  have hu : ∀ a b c : A, a - b ^ q ∈ N → a - c ^ q ∈ N → b ^ q = c ^ q := by
    intro a b c hb hc
    have h1 : (b - c) ^ q ∈ N := by
      rw [hqdef, sub_pow_char_pow]
      have : b ^ p ^ (n + 1) - c ^ p ^ (n + 1) = (a - c ^ q) - (a - b ^ q) := by ring
      rw [this]
      exact N.sub_mem hc hb
    have h2 : b - c ∈ N := mem_nilradical.mpr (IsNilpotent.of_pow (mem_nilradical.mp h1))
    have h3 := hq _ h2
    rw [hqdef, sub_pow_char_pow, sub_eq_zero] at h3
    exact h3
  choose β hβ using hlift
  have hf : ∀ a c : A, a - c ^ q ∈ N → β a ^ q = c ^ q := fun a c hc => hu a _ _ (hβ a) hc
  let π : A →ₐ[k] A :=
    { toFun := fun a => β a ^ q
      map_one' := by
        rw [hf 1 1 (by simp), one_pow]
      map_mul' := fun x y => by
        rw [hf (x * y) (β x * β y) ?_, mul_pow]
        have : x * y - (β x * β y) ^ q = x * (y - β y ^ q) + (x - β x ^ q) * β y ^ q := by ring
        rw [this]
        exact N.add_mem (N.mul_mem_left _ (hβ y)) (N.mul_mem_right _ (hβ x))
      map_zero' := by
        rw [hf 0 0 (by rw [zero_pow (by positivity), sub_zero]; exact N.zero_mem), zero_pow (by positivity)]
      map_add' := fun x y => by
        rw [hf (x + y) (β x + β y) ?_, hqdef, add_pow_char_pow]
        rw [hqdef, add_pow_char_pow]
        have : x + y - (β x ^ p ^ (n + 1) + β y ^ p ^ (n + 1)) =
            (x - β x ^ q) + (y - β y ^ q) := by rw [hqdef]; ring
        rw [this]
        exact N.add_mem (hβ x) (hβ y)
      commutes' := fun c => by
        set d := (iterateFrobeniusEquiv k p (n + 1)).symm c with hd
        have hdc : d ^ q = c := by
          have h0 := RingEquiv.apply_symm_apply (iterateFrobeniusEquiv k p (n + 1)) c
          rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at h0
          rw [hqdef, hd]
          exact h0
        rw [hf _ (algebraMap k A d) ?_, ← map_pow, hdc]
        rw [← map_pow, hdc, sub_self]
        exact N.zero_mem }
  have hπ : ∀ a, π a = β a ^ q := fun a => rfl
  refine ⟨π, fun a => ?_, fun a => ⟨β a ^ p ^ n, ?_⟩⟩
  · rw [hπ]
    exact mem_nilradical.mp (hβ a)
  · rw [map_pow, ← pow_mul, ← pow_succ, hπ a]
    have h2 : β a - π (β a) ∈ N := mem_nilradical.mpr (by rw [hπ]; exact mem_nilradical.mp (hβ _))
    have h3 := hq _ h2
    rw [hqdef, sub_pow_char_pow, sub_eq_zero] at h3
    exact h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutData
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

set_option backward.isDefEq.respectTransparency false in
theorem isClosedImmersion_toSpecΓ_comp {X : Scheme.{0}} (O : X.Opens) (hO : IsAffineOpen O)
    {A : CommRingCat.{0}} (q : A ⟶ Γ(X, O)) (h : Function.Surjective q.hom) :
    IsClosedImmersion (O.toSpecΓ ≫ Spec.map q) := by
  have := IsClosedImmersion.spec_of_surjective _ h
  rw [← hO.isoSpec_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem surjective_toSpecΓ_comp {X : Scheme.{0}} (O : X.Opens) (hO : IsAffineOpen O)
    {A : CommRingCat.{0}} (q : A ⟶ Γ(X, O)) (h : Function.Surjective q.hom)
    (h' : IsNilpotent (RingHom.ker q.hom)) : Surjective (O.toSpecΓ ≫ Spec.map q) := by
  have : Surjective (Spec.map q) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap q.hom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ h,
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn] at this
  rw [← hO.isoSpec_hom]
  infer_instance

theorem mem_upOpen_iff {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (x : Y₀) : i x ∈ upOpen i U ↔ x ∈ U :=
  SetLike.ext_iff.mp (preimage_upOpen i U) x


set_option backward.isDefEq.respectTransparency false in
theorem exists_pushout_data : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ Surjective j₁ ∧ Surjective j₂ ∧ ∃ 𝒱 : Set Y.Opens, TopologicalSpace.Opens.IsBasis 𝒱 ∧ ∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ hc₁ hc₂ hs₁ hs₂ hn₁ hn₂
  haveI := hc₁; haveI := hc₂; haveI := hs₁; haveI := hs₂
  have hR : ∀ U ∈ good i₁ i₂, _ := fun U (hU : U ∈ good i₁ i₂) ↦
    _root_.GlobalTheory.pullbackCone_fst_snd_ring_nilpotent (res i₁ U) (res i₂ U) (_root_.GlobalTheory.FerrandPush.res_surjective_nilpotent_ker i₁ hn₁ U hU.2.1).1 (_root_.GlobalTheory.FerrandPush.res_surjective_nilpotent_ker i₁ hn₁ U hU.2.1).2
      (_root_.GlobalTheory.FerrandPush.res_surjective_nilpotent_ker i₂ hn₂ U hU.2.2).1 (_root_.GlobalTheory.FerrandPush.res_surjective_nilpotent_ker i₂ hn₂ U hU.2.2).2
  have hπ : ∀ U ∈ good i₁ i₂, Function.Surjective ((fibπ i₁ i₂).app (op U)).hom ∧
      IsNilpotent (RingHom.ker ((fibπ i₁ i₂).app (op U)).hom) := fun U hU ↦ (hR U hU).2.2
  have hbas₀ : ∀ U ∈ good i₁ i₂, ∀ (W : Y₀.Opens) (x : Y₀), x ∈ U → x ∈ W →
      ∃ V ∈ good i₁ i₂, x ∈ V ∧ V ≤ U ∧ V ≤ W := by
    intro U hU W x hxU hxW
    obtain ⟨f, hf, hxf⟩ := hU.1.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
    obtain ⟨a, rfl⟩ := (hπ U hU).1 f
    exact ⟨_, GlobalTheory.T.ferrand_pushout_good_basic_open i₁ i₂ U hU a, hxf, Y₀.basicOpen_le _, hf⟩
  have hopen := GlobalTheory.T.isOpenImmersion_of_nilpotent_thickening_cover Y₀ (good i₁ i₂) (fun U hU ↦ hU.1) (fib i₁ i₂) (fibπ i₁ i₂) hπ (GlobalTheory.T.isLocalization_away_ferrandPush_fib i₁ i₂)
  let F := ThickGlue.specDiagram (good i₁ i₂) (fib i₁ i₂)
  haveI hF : ∀ {U V : good i₁ i₂} (f : U ⟶ V), IsOpenImmersion (F.map f) :=
    fun {U V} f ↦ hopen _ U.2 _ V.2 f.le
  haveI : (F ⋙ Scheme.forget).IsLocallyDirected :=
    _root_.GlobalTheory.ThickGlue.isLocallyDirected_of_basis (good i₁ i₂) (fun U hU V _ x hx hy ↦ hbas₀ U hU V x hx hy) F hF
      (fun U ↦ ThickGlue.toSpec (fibπ i₁ i₂) U.1)
      (fun U ↦ by
        haveI := ThickGlue.isClosedImmersion_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1
        exact (ThickGlue.toSpec _ U.1).isClosedEmbedding.injective)
      (fun U ↦ by
        haveI := ThickGlue.surjective_toSpec (fibπ i₁ i₂) U.2.1 (hπ U.1 U.2).1 (hπ U.1 U.2).2
        exact (ThickGlue.toSpec _ U.1).surjective)
      (fun h ↦ ThickGlue.toSpec_naturality _ h)
  let e₁ : ∀ U : good i₁ i₂, (upOpen i₁ U.1).toScheme ⟶ F.obj U := fun U ↦
    (upOpen i₁ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).fst
  let e₂ : ∀ U : good i₁ i₂, (upOpen i₂ U.1).toScheme ⟶ F.obj U := fun U ↦
    (upOpen i₂ U.1).toSpecΓ ≫ Spec.map (cone i₁ i₂ U.1).snd
  have hn1 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₁.homOfLE (upOpen_mono i₁ h) ≫ e₁ V =
      e₁ U ≫ F.map (homOfLE (show U ≤ V from h)) := by
    intro U V h
    change _ = _ ≫ Spec.map (fibMap i₁ i₂ h)
    simp only [e₁]
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, fibMap_fst]
  have hn2 : ∀ {U V : good i₁ i₂} (h : U.1 ≤ V.1), Y₂.homOfLE (upOpen_mono i₂ h) ≫ e₂ V =
      e₂ U ≫ F.map (homOfLE (show U ≤ V from h)) := by
    intro U V h
    change _ = _ ≫ Spec.map (fibMap i₁ i₂ h)
    simp only [e₂]
    rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, fibMap_snd]
  have hbasK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik],
      ∀ U ∈ good i₁ i₂, ∀ V ∈ good i₁ i₂, ∀ y : Yk, y ∈ upOpen ik U → y ∈ upOpen ik V →
        ∃ W ∈ good i₁ i₂, y ∈ upOpen ik W ∧ W ≤ U ∧ W ≤ V := by
    intro Yk ik _ _ U hU V _ y hyU hyV
    obtain ⟨x, rfl⟩ := ik.surjective y
    rw [mem_upOpen_iff] at hyU hyV
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas₀ U hU V x hyU hyV
    exact ⟨W, hW, (mem_upOpen_iff ik W x).2 hxW, h1, h2⟩
  have hcovK : ∀ {Yk : Scheme.{0}} (ik : Y₀ ⟶ Yk) [IsClosedImmersion ik] [Surjective ik],
      ∀ y : Yk, ∃ U ∈ good i₁ i₂, y ∈ upOpen ik U := by
    intro Yk ik _ _ y
    obtain ⟨x, rfl⟩ := ik.surjective y
    obtain ⟨U, hU, hx⟩ := _root_.GlobalTheory.FerrandPush.exists_good_mem i₁ i₂ x
    exact ⟨U, hU, (mem_upOpen_iff ik U x).2 hx⟩
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hbasK i₁)
    (hcovK i₁) e₁ hn1
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.exists_glue_to_locallyDirected_colimit_of_basis (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hbasK i₂)
    (hcovK i₂) e₂ hn2
  obtain ⟨ci₁, su₁, pre₁⟩ := _root_.GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage (good i₁ i₂) F Y₁ (upOpen i₁) (upOpen_mono i₁) (hcovK i₁) e₁
    (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1)
    (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.1 _ (hR U.1 U.2).1.1 (hR U.1 U.2).1.2) hn1 j₁ hj₁
  obtain ⟨ci₂, su₂, pre₂⟩ := _root_.GlobalTheory.GlueColim.isClosedImmersion_surjective_preimage (good i₁ i₂) F Y₂ (upOpen i₂) (upOpen_mono i₂) (hcovK i₂) e₂
    (fun U ↦ isClosedImmersion_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1)
    (fun U ↦ surjective_toSpecΓ_comp _ U.2.2.2 _ (hR U.1 U.2).2.1.1 (hR U.1 U.2).2.1.2) hn2 j₂ hj₂
  have key1 : ∀ U : good i₁ i₂, U.1.ι ≫ i₁ ≫ j₁ =
      U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).fst ≫ res i₁ U.1) ≫ colimit.ι F U := by
    intro U
    rw [← Scheme.Hom.resLE_comp_ι_assoc i₁ (preimage_upOpen i₁ U.1).ge, hj₁ U]
    simp only [e₁, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have key2 : ∀ U : good i₁ i₂, U.1.ι ≫ i₂ ≫ j₂ =
      U.1.toSpecΓ ≫ Spec.map ((cone i₁ i₂ U.1).snd ≫ res i₂ U.1) ≫ colimit.ι F U := by
    intro U
    rw [← Scheme.Hom.resLE_comp_ι_assoc i₂ (preimage_upOpen i₂ U.1).ge, hj₂ U]
    simp only [e₂, res, Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have hw : i₁ ≫ j₁ = i₂ ≫ j₂ := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨U, hU, hx⟩ := _root_.GlobalTheory.FerrandPush.exists_good_mem i₁ i₂ x
    refine ⟨U, hx, ?_⟩
    rw [key1 ⟨U, hU⟩, key2 ⟨U, hU⟩, (cone i₁ i₂ U).condition]
  have h0 : ∀ U : good i₁ i₂, (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    intro U
    change i₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ (colimit.ι F U).opensRange) = U.1
    rw [pre₁ U, preimage_upOpen]
  refine ⟨colimit F, j₁, j₂, hw, ci₁, ci₂, su₁, su₂,
    Set.range (fun U : good i₁ i₂ ↦ (colimit.ι F U).opensRange), ?_, ?_⟩
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O y hy
    obtain ⟨x, rfl⟩ := (i₁ ≫ j₁).surjective y
    obtain ⟨U₀, hU₀, hx₀⟩ := _root_.GlobalTheory.FerrandPush.exists_good_mem i₁ i₂ x
    obtain ⟨U, hU, hxU, -, hUO⟩ := hbas₀ U₀ hU₀ ((i₁ ≫ j₁) ⁻¹ᵁ O) x hx₀ hy
    refine ⟨_, ⟨⟨U, hU⟩, rfl⟩, ?_, ?_⟩
    · show x ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange
      rw [h0 ⟨U, hU⟩]
      exact hxU
    · intro z hz
      obtain ⟨x', rfl⟩ := (i₁ ≫ j₁).surjective z
      have hx' : x' ∈ (i₁ ≫ j₁) ⁻¹ᵁ (colimit.ι F ⟨U, hU⟩).opensRange := hz
      rw [h0 ⟨U, hU⟩] at hx'
      exact hUO hx'
  · rintro _ ⟨U, rfl⟩
    have hle : ⊤ ≤ (colimit.ι F U) ⁻¹ᵁ (colimit.ι F U).opensRange := fun x _ ↦ ⟨x, rfl⟩
    haveI hiso : IsIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) := by
      have := (colimit.ι F U).isIso_app (colimit.ι F U).opensRange le_rfl
      have : IsIso (homOfLE hle) := homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm
      rw [Scheme.Hom.appLE]
      infer_instance
    let ψ : Γ(colimit F, (colimit.ι F U).opensRange) ≅ (fib i₁ i₂).obj (op U.1) :=
      asIso ((colimit.ι F U).appLE (colimit.ι F U).opensRange ⊤ hle) ≪≫ Scheme.ΓSpecIso _
    have a1 := GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₁ (upOpen i₁ U.1)
      (cone i₁ i₂ U.1).fst (pre₁ U) (hj₁ U)
    have a2 := GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor (A := (fib i₁ i₂).obj (op U.1)) (colimit.ι F U) j₂ (upOpen i₂ U.1)
      (cone i₁ i₂ U.1).snd (pre₂ U) (hj₂ U)
    have P := IsPullback.of_isLimit (coneIsLimit i₁ i₂ U.1)
    refine P.of_iso ψ.symm (Y₁.presheaf.mapIso (eqToIso (pre₁ U)).op)
      (Y₂.presheaf.mapIso (eqToIso (pre₂ U)).op) (Y₀.presheaf.mapIso (eqToIso (h0 U)).op)
      ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.eq_inv_comp]
      simp only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
        eqToIso.hom]
      rw [← reassoc_of% a1]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]
    · rw [Iso.symm_hom, Iso.eq_inv_comp]
      simp only [ψ, Iso.trans_hom, asIso_hom, Category.assoc, Functor.mapIso_hom, Iso.op_hom,
        eqToIso.hom]
      rw [← reassoc_of% a2]
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map_assoc]
    · simp only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]
    · simp only [res, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Scheme.Hom.appLE_map,
        Scheme.Hom.map_appLE]

end GlobalTheory.FerrandPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslationStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := n)), ∃ g, GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  first | exact @GlobalTheory.LFun.tn_single | exact GlobalTheory.LFun.tn_single | (intros; apply GlobalTheory.LFun.tn_single <;> assumption)
end

