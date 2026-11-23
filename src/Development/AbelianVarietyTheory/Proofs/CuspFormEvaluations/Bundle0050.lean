module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_iff_modN (k : ℕ) (x : Dw.La) :
    x ∈ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) ↔ Dw.ModN k x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩,
    fun ⟨b, hb⟩ => ⟨b, trivial, by rw [hb, Nat.cast_smul_eq_nsmul]⟩⟩

theorem mk_eq_iff (k : ℕ) (a b : Dw.La) :
    (Submodule.Quotient.mk a : LatMod Dw k) = Submodule.Quotient.mk b ↔ Dw.ModN k (a - b) := by
  rw [Submodule.Quotient.eq, mem_iff_modN]

theorem finite_latMod (k : ℕ) (hk : 0 < k) : Finite (LatMod Dw k) := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw k hk
  refine Finite.of_surjective (fun j => (Submodule.Quotient.mk (r j) : LatMod Dw k)) fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨π a, (mk_eq_iff k _ _).2 ((hπ _ _).1 (hr _))⟩

theorem nsmul_latMod (k : ℕ) (q : LatMod Dw k) : k • q = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_iff_modN]
  exact ⟨a, Nat.cast_smul_eq_nsmul _ _ _⟩

variable (Xo : Moduli Dw l)

theorem exists_descend (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : Dw.La → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hlin : ∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) (hker : ∀ a, ev (k • a) = 1)
    (hinj : ∀ (K : Type) [Field K] (χ : S →+* K) (a b : Dw.La),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b)) :
    ∃ ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G), IsFullLev Xo k x0 ev' ∧
      ∀ a, ev' (Submodule.Quotient.mk a) = ev a := by
  choose r hr using Submodule.Quotient.mk_surjective (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)
  have h : ∀ a, ev (r (Submodule.Quotient.mk a)) = ev a := fun a => by
    obtain ⟨b, hb⟩ := (mk_eq_iff k _ _).1 (hr (Submodule.Quotient.mk a))
    rw [sub_eq_iff_eq_add.1 hb, hadd, hker, _root_.one_mul]
  refine ⟨fun q => ev (r q), ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => ?_⟩, h⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    beta_reduce
    rw [← Submodule.Quotient.mk_add, h, h, h, hadd]
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, h, h, hlin]
  · rw [← hr a, ← hr b]
    exact (mk_eq_iff k _ _).2 (hinj K χ _ _ hab)

theorem pow_eq_one {k : ℕ} {S : Type} [CommRing S] {x0 : Sp S ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (h : IsFullLev Xo k x0 ev) (q : LatMod Dw k) : ev q ^ k = 1 := by
  let f : LatMod Dw k →+ Additive (ptO Xo x0 ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (h.1 a b)
  have := map_nsmul f k q
  rw [nsmul_latMod, map_zero] at this
  exact (congrArg Additive.toMul this).symm

theorem baseChange {k : ℕ} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x0 : Sp S ⟶ Xo.X}
    {x1 : Sp T ⟶ Xo.X} (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ)
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) :
    IsFullLev Xo k x1 (fun q => h ≫ ev q) := by
  refine ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => hev.2.2 K (χ.comp ψ) a b ?_⟩
  · beta_reduce
    rw [hev.1, MonObj.comp_mul]
  · beta_reduce
    rw [hev.2.1, Category.assoc]
  · have : spMap χ ≫ h.left ≫ (ev a).left = spMap χ ≫ h.left ≫ (ev b).left := hab
    rw [hh] at this
    rw [spMap_comp, Category.assoc, Category.assoc]
    exact this

theorem eq_of_agree (hL : Laws) {k : ℕ} (hk : 0 < k) {S T : Type} [CommRing S] [CommRing T] (χ : S →+* T)
    (hχ : ∀ e, χ e = 1 → IsUnit e) {x0 : Sp S ⟶ Xo.X} {a b : ptO Xo x0 ⟶ Xo.univ.t.G} (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hab : spMap χ ≫ a.left = spMap χ ≫ b.left) : a = b := by
  obtain ⟨e, he, He⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo S x0 k hk a b ha hb
  have h1 : e = 1 := (hχ e ((He T χ).2 hab)).mul_left_cancel (he.eq.trans (_root_.mul_one _).symm)
  have h2 := (He S (RingHom.id S)).1 h1
  have h3 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id (CommRingCat.of S)
  rw [h3] at h2
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans (h2.trans (Category.id_comp _)))

theorem exists_geometric (hL : Laws) {k : ℕ} (hk : 0 < k) (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X) :
    ∃ ev, IsFullLev Xo k x0 ev ∧ ∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x0 ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x0 β.hom hβ.symm
  obtain ⟨ev, hev, h⟩ := exists_descend Xo k x0 (I.ev k) (I.add k) (I.lin k) (fun a => (I.ker k hk _).2 ⟨a, rfl⟩)
    fun K' _ χ a b hab => by
      have h1 : I.ev k a = I.ev k b :=
        eq_of_agree Xo hL hk χ (fun e he => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at he)
          ((I.onto k hk _).2 ⟨_, rfl⟩) ((I.onto k hk _).2 ⟨_, rfl⟩) hab
      have h2 : I.ev k a = I.ev k (a - b) * I.ev k b := by rw [← I.add, sub_add_cancel]
      rw [h2, mul_eq_right, I.ker k hk] at h1
      exact h1
  refine ⟨ev, hev, fun p hp => ?_⟩
  obtain ⟨a, ha⟩ := (I.onto k hk p).1 hp
  exact ⟨_, (h a).trans ha⟩

theorem onto_of_local (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (p : ptO Xo x0 ⟶ Xo.univ.t.G)
    (hp : p ^ k = 1) : ∃ q, ev q = p := by
  haveI := finite_latMod (Dw := Dw) k hk
  let K := AlgebraicClosure (IsLocalRing.ResidueField T)
  let χ : T →+* K := (algebraMap (IsLocalRing.ResidueField T) K).comp (IsLocalRing.residue T)
  have hχ : ∀ e, χ e = 1 → IsUnit e := fun e he => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    simp [χ, h0] at he
  let h : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  obtain ⟨ev₀, -, h₀⟩ := exists_geometric Xo hL hk K (spMap χ ≫ x0)
  have hpow : ∀ a : ptO Xo x0 ⟶ Xo.univ.t.G, a ^ k = 1 → (h ≫ a) ^ k = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  choose f hf using fun q => h₀ (h ≫ ev q) (hpow _ (pow_eq_one Xo hev q))
  have hinj : Function.Injective f := fun a b hab => hev.2.2 K χ a b
    (congrArg CommaMorphism.left ((hf a).symm.trans ((congrArg ev₀ hab).trans (hf b))))
  obtain ⟨r, hr⟩ := h₀ (h ≫ p) (hpow p hp)
  obtain ⟨q, rfl⟩ := Finite.surjective_of_injective hinj r
  exact ⟨q, eq_of_agree Xo hL hk χ hχ (pow_eq_one Xo hev q) hp
    (congrArg CommaMorphism.left ((hf q).symm.trans hr))⟩

theorem injective_of_local {k : ℕ} {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) : Function.Injective ev :=
  fun a b hab => hev.2.2 _ (IsLocalRing.residue T) a b (by rw [hab])

theorem exists_levGrp (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (hev' : IsFullLev Xo k x0 ev') :
    ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q) := by
  haveI := finite_latMod (Dw := Dw) k hk
  choose f hf using fun q => onto_of_local Xo hL hk hev (ev' q) (pow_eq_one Xo hev' q)
  have hi := injective_of_local Xo hev
  let g : LatMod Dw k →ₗ[𝓞 E] LatMod Dw k :=
    { toFun := f
      map_add' := fun a b => hi (by rw [hev.1, hf, hf, hf, hev'.1])
      map_smul' := fun o a => hi (by rw [RingHom.id_apply, hev.2.1, hf, hf, hev'.2.1]) }
  have hg : Function.Injective g := fun a b hab => injective_of_local Xo hev'
    ((hf a).symm.trans ((congrArg ev hab).trans (hf b)))
  exact ⟨LinearEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, fun q => (hf q).symm⟩

end FullLevel


open FullLevel in
theorem fullLevel_cover_baseChange_torsor :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : ℕ), 0 < k → (∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X), ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : LatMod Dw k → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ IsFullLev Xo k (spMap φ ≫ x0) ev) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ ev, IsFullLev Xo k x0 ev → IsFullLev Xo k x1 (fun q => h ≫ ev q) ∧ ∀ q, ev q ^ k = 1) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)), IsFullLev Xo k x0 ev → (∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p) ∧ ∀ ev', IsFullLev Xo k x0 ev' → ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X), ∃ ev, IsFullLev Xo k x0 ev := by
  intro hL E _ _ _ H Dw l Xo k hk
  refine ⟨fun S _ x0 => ?_, fun S T _ _ ψ x0 x1 h hh ev hev => ⟨FullLevel.baseChange Xo ψ h hh hev, FullLevel.pow_eq_one Xo hev⟩,
    fun T _ _ x0 ev hev => ⟨FullLevel.onto_of_local Xo hL hk hev, fun ev' hev' => FullLevel.exists_levGrp Xo hL hk hev hev'⟩,
    fun K _ _ x0 => (FullLevel.exists_geometric Xo hL hk K x0).imp fun _ h => h.1⟩
  obtain ⟨B, _, φ, ev, hφ, h1, h2, h3, h4⟩ := exists_faithfullyFlat_linear_level hL E H Dw l Xo S x0 k hk
  obtain ⟨ev', hev', -⟩ := FullLevel.exists_descend Xo k (spMap φ ≫ x0) ev h1 h2 h3 h4
  exact ⟨B, inferInstance, φ, ev', hφ, hev'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HmEqDiagonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HermDiag

private theorem hermForm_eq_star_swap {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsHermitian)
    (z w : Fin g → ℂ) : hermForm A z w = star (hermForm A w z) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply j i]
  ring

private theorem eq_of_im_hermForm_eq_of_real_span_eq_univ {g : ℕ} {La : Type} [AddCommGroup La] (A B : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (P : La →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (h : ∀ a b, (hermForm A (P a) (P b)).im = (hermForm B (P a) (P b)).im) : A = B := by
  let L : (Fin g → ℂ) → (Fin g → ℂ) →ₗ[ℝ] ℝ := fun w =>
    { toFun := fun z => (hermForm A z w).im - (hermForm B z w).im
      map_add' := fun z z' => by
        simp only [hermForm, add_dotProduct, Complex.add_im]; ring
      map_smul' := fun t z => by
        simp only [hermForm, smul_dotProduct, Complex.smul_im, RingHom.id_apply, smul_eq_mul]; ring }
  have hL : ∀ w z, L w z = (hermForm A z w).im - (hermForm B z w).im := fun _ _ => rfl
  have zero_of : ∀ w, (∀ a, L w (P a) = 0) → ∀ z, L w z = 0 := by
    intro w hw z
    have h0 : L w = 0 := LinearMap.ext_on hP (fun y hy => by
      obtain ⟨a, rfl⟩ := hy
      simpa using hw a)
    rw [h0]; rfl
  have key1 : ∀ a z, L (P a) z = 0 := fun a => zero_of _ (fun b => by rw [hL, h b a, sub_self])
  have key2 : ∀ z w, L w z = 0 := by
    intro z w
    refine zero_of w (fun a => ?_) z
    have h1 := key1 a w
    rw [hL] at h1 ⊢
    rw [hermForm_eq_star_swap A hA (P a) w, hermForm_eq_star_swap B hB (P a) w]
    simp only [Complex.star_def, Complex.conj_im]
    linarith
  ext i j
  apply Complex.ext
  · have h1 := key2 (Pi.single i Complex.I) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith
  · have h1 := key2 (Pi.single i 1) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu hg hU ho
  obtain ⟨hr, htype, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := htype k
  have hbij : Function.Bijective (relab c σ) := by
    rw [← Finite.injective_iff_bijective]
    intro τ₁ τ₂ h12
    ext y
    have h1 : σ (Formalism.L2.Pj.embF c τ₁ y) = σ (Formalism.L2.Pj.embF c τ₂ y) :=
      congrArg (fun f : E →+* ℂ => f y) h12
    exact congrArg Subtype.val (σ.injective h1)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
      simpa using this
    have h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  have hkey : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    have hg' : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hg
    have hρ : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases hsq τ with h | h
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hρ.symm)
      have h3 : relab c σ τ (H.rt : E) = H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = H.rt0
        rw [e, hg']
      rw [h3, h]
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = -IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (by
          show τ (H.rt : E) = -((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
          rw [h, hρ])
      have h3 : relab c σ τ (H.rt : E) = -H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = -H.rt0
        rw [e, map_neg, hg']
      rw [h3, h]
  have hpm : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → Dw.mult τ = Dw.p := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_pos hτ]
  have hqm : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = Dw.q := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_neg hτ]
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult hpm hqm
  set idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f with hidx
  have hz : ∀ a j, W.Pm a j = if ((idx j).2 : ℕ) < Dw.q then
      FD.hermC (idx j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 (idx j).1) (idx j).2)
        (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))
      else ((FD.mat x.1 (idx j).1)⁻¹.mulVec (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))) (idx j).2 := by
    intro a j
    rw [W.pm_eq a j]
    unfold Formalism.L2.Pj.perFr
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨hin, h1, h2⟩ | ⟨hout, h1, h2, h3⟩
    · have hi : (U.X k).p0 + ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dite_eq_left hin, dite_eq_left hi, if_neg (by omega)]
      have e1 : (f (W.e j)).1 = ⟨relab c σ (W.e j).1, hin⟩ := Subtype.ext h1
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 + ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 + ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
    · have hcj : conjEmb (relab c σ (W.e j).1) = (f (W.e j)).1.1 := by
        rw [h1]
        exact RingHom.ext fun y => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      have hin' : conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ := by
        rw [hcj]
        exact (f (W.e j)).1.2
      have hi : (U.X k).p0 - 1 - ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dite_eq_right hout, dite_eq_left hin', dite_eq_left hi, if_pos (by omega)]
      have e1 : (f (W.e j)).1 = ⟨conjEmb (relab c σ (W.e j).1), hin'⟩ := Subtype.ext hcj.symm
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 - 1 - ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 - 1 - ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have hx : ∀ τ : (U.X k).Ψ, FD.gram τ.1 (U.X k).Gm (FD.mat x.1 τ) =
      Matrix.diagonal fun a : Fin r => ((FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    rw [← hp0]
    exact ho τ
  set D0 : Matrix (Fin W.g) (Fin W.g) ℂ :=
    Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) with hD0
  have hD : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im = (hermForm D0 (W.Pm a) (W.Pm b)).im := by
    intro a b
    rw [Wu.c1 a b, hD0, GlobalTheory.OrthoHerm.im_diag_eq_trace Dw.q (-(U.X k).ξ0) (U.X k).Gm (U.X k).Ψ
      (U.X k).cmType idx hcc x.1 hx (W.φ k a : Fin r → E) (W.φ k b : Fin r → E) (W.Pm a) (W.Pm b)
      (hz a) (hz b), ← W.isom k a b]
    push_cast
    rfl
  have hD0h : D0.IsHermitian := by
    rw [hD0]
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext j
    simp
  obtain ⟨-, -, -, hspan, -⟩ := W.per
  have hHm : Wu.Hm = D0 := eq_of_im_hermForm_eq_of_real_span_eq_univ Wu.Hm D0 Wu.herm hD0h W.Pm hspan hD
  rw [hHm, hD0]
  congr 1
  funext j
  have hpos := Wu.pos (Pi.single j 1) (by simp)
  rw [hHm, hD0] at hpos
  have hdiag : (hermForm (Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ))
      (Pi.single j 1) (Pi.single j 1)).re = 2 * ((idx j).1.1 (-(U.X k).ξ0)).im := by
    simp [hermForm]
  rw [hdiag, map_neg, Complex.neg_im] at hpos
  have hre : ((idx j).1.1 (U.X k).ξ0).re = 0 := by
    have h1 : starRingEnd ℂ ((idx j).1.1 (U.X k).ξ0) = -((idx j).1.1 (U.X k).ξ0) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj (φ := (idx j).1.1) (x := (U.X k).ξ0),
        ← map_neg]
      congr 1
      exact (U.X k).ξ0_im
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hnorm : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖(idx j).1.1 (U.X k).ξ0‖ := by
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1]
    · rw [h1, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  have hfin : ((idx j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    rw [hnorm, ← (Complex.abs_im_eq_norm).mpr hre, map_neg, Complex.neg_im,
      abs_of_neg (by linarith)]
  rw [hfin]

end GlobalTheory.HermDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NegLogSqrtLeOfJbound
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem neg_log_sqrt_le_of_jbound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (dg n : ℕ) (P : I2.Par X dg) (S tableLineDegreeFive cc : ℝ), (Real.pi⁻¹) ^ dg * P.Jbound n ≤ S → p14 E X.r n P.m ≤ tableLineDegreeFive → 8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q ≤ cc → -Real.log (Real.sqrt S) ≤ tableLineDegreeFive * dg + cc * P.ph := by
  intro E _ _ _ X dg n P S tableLineDegreeFive cc hS hP14 hcc
  have hf : 0 < I2.PT.f E := by
    have h1 := P.hfr
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  have hdp : 0 < I2.dstar (E := E) P.m := Nat.mul_pos (Nat.mul_pos two_pos hf) P.hm1
  have hd0 : (1 : ℝ) ≤ (I2.dstar (E := E) P.m : ℝ) := by exact_mod_cast hdp
  have hd : (0 : ℝ) < 2 * (I2.dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((I2.dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  have hph : 0 ≤ P.ph := by
    unfold I2.Par.ph I2.PT.ph
    split_ifs <;> positivity
  have hA : (4 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
  have hBn : (6 * (2 * (I2.dstar (E := E) P.m : ℝ)) ^ ((I2.dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero h6.ne')
  have hC : (2 : ℝ)⁻¹ ^ ((X.r + 2) * dg) ≠ 0 := by positivity
  have hJpos : 0 < P.Jbound n := by
    unfold I2.Par.Jbound
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
      (pow_pos (by norm_num) _)) (Real.exp_pos _)
  have hJ : Real.log (P.Jbound n) = -(n * Real.log 4) -
      n * (Real.log 6 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ))) -
      (((X.r + 2) * dg : ℕ) : ℝ) * Real.log 2 -
      2 * (8100 * Real.pi * n * (P.m : ℝ) ^ 4 * (I2.dstar (E := E) P.m : ℝ) ^ 4 * I2.RR (E := E) / P.q * P.ph) := by
    unfold I2.Par.Jbound
    rw [Real.log_mul (mul_ne_zero (mul_ne_zero hA hBn) hC) (Real.exp_pos _).ne',
      Real.log_mul (mul_ne_zero hA hBn) hC, Real.log_mul hA hBn, Real.log_exp, Real.log_pow,
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_inv, Real.log_inv,
      Real.log_mul (by norm_num) hB.ne', Real.log_rpow hd]
    unfold I2.Cchi
    ring
  have hdg : (1 : ℝ) ≤ dg := by exact_mod_cast P.hDF
  have h24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl2d : 0 ≤ Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := Real.log_nonneg (by linarith)
  have hT : 0 ≤ Real.log 24 + (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by
    have : 0 < Real.log 24 := Real.log_pos (by norm_num)
    have : 0 ≤ (I2.dstar (E := E) P.m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) P.m : ℝ)) := by positivity
    linarith
  have hpi : (0 : ℝ) < (Real.pi⁻¹) ^ dg := pow_pos (inv_pos.2 Real.pi_pos) _
  have hpos : 0 < (Real.pi⁻¹) ^ dg * P.Jbound n := mul_pos hpi hJpos
  have hlS := Real.log_le_log hpos hS
  rw [Real.log_mul hpi.ne' hJpos.ne', Real.log_pow, Real.log_inv, hJ] at hlS
  rw [Real.log_sqrt (hpos.le.trans hS)]
  have e2 := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hT) (sub_nonneg.2 hdg)
  have e3 := mul_le_mul_of_nonneg_right hcc hph
  have e4 := mul_le_mul_of_nonneg_right hP14 (by linarith : (0 : ℝ) ≤ dg)
  unfold p14 at e4
  push_cast at hlS
  rw [h24] at e2 e4
  linarith [e2, e3, e4]

end GlobalTheory.AnVal
end

