module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCove
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.AffRad

theorem C_dvd_of_C_dvd_pow {A σ : Type} [CommRing A] {g : A} (hg : ∀ (x : A) (n : ℕ), g ∣ x ^ n → g ∣ x)
    {P : MvPolynomial σ A} {n : ℕ} (h : MvPolynomial.C g ∣ P ^ n) : MvPolynomial.C g ∣ P := by
  have hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq] at h ⊢
  rw [map_pow] at h
  have hn := (MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩
  apply MvPolynomial.ext
  intro i
  obtain ⟨k, hk⟩ := hn i
  rw [MvPolynomial.coeff_map] at hk ⊢
  rw [← map_pow, hq] at hk
  change Ideal.Quotient.mk (Ideal.span {g}) (P.coeff i) = 0
  exact (hq _).2 (hg _ _ hk)

theorem exists_div_of_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
    {V : M.Z.Opens} (hV : IsAffineOpen V) {z : M.Z} (hz : z ∈ V) {x : Ω} (hx : x ∈ M.O z) :
    ∃ a b : Ω, a ∈ M.ringOn V ∧ b ∈ M.ringOn V ∧ b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x * b = a := by
  obtain ⟨U, f, hU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply,
    RatModel.res_apply] at h1
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)
  refine ⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩
  rw [← inv_pow]
  exact pow_mem hu.2 n

theorem keepsRad_of_affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ)
    (h : AffCover M M' φ f r) : KeepsRad M M' φ f := by
  rintro z' g ⟨hg0, hgO, hg⟩
  obtain ⟨hf, hc⟩ := h
  obtain ⟨U, W, t, hU, -, hz, hW, hinj, hR⟩ := hc z'
  have hφ0 : φ g ≠ 0 := (map_ne_zero φ).2 hg0
  refine ⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩
  let A := (M.O (f z')).toSubring
  let ψ : MvPolynomial (Fin r) A →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro P hP
    have := hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this
  have hO : ∀ P, ψ P ∈ M'.O z' := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C]; exact hf.map_mem_O a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))
  have hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y := by
    intro y hy
    rw [hR] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩
      · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩
    | algebraMap c =>
      exact ⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩,
        (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩
    | add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, map_add _ _ _⟩
    | mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, map_mul _ _ _⟩
  have hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y := by
    rintro y k ⟨c, hc⟩
    have e : (y : Ω) ^ k = g * c := congrArg Subtype.val hc
    have := hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)
    exact ⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩
  have hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g := MvPolynomial.eval₂Hom_C _ _ _
  obtain ⟨a, b, ha, hb, hb0, hbi, e1⟩ := exists_div_of_mem_O hU hz hx
  obtain ⟨c, d, hc, hd, hd0, hdi, e2⟩ := exists_div_of_mem_O hU hz hxn
  obtain ⟨a, rfl⟩ := hS a ha
  obtain ⟨b, rfl⟩ := hS b hb
  obtain ⟨c, rfl⟩ := hS c hc
  obtain ⟨d, rfl⟩ := hS d hd
  have hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1) := by
    refine ⟨c * b ^ n * a * d ^ n, hψ ?_⟩
    simp only [map_mul, map_pow, hC, ← e2]
    rw [← e1]
    field_simp
    ring
  obtain ⟨Q, hQ⟩ := C_dvd_of_C_dvd_pow hrad hdvd
  have e3 := congrArg ψ hQ
  rw [map_mul, map_mul, hC, ← e1] at e3
  have e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹ := by
    field_simp
    linear_combination e3
  rw [e4]
  exact mul_mem (mul_mem (hO Q) hbi) hdi

end GlobalTheory.FlagBundle.AffRad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.ProjPts

open GlobalTheory.ZH.RatModel GlobalTheory.Points

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
  {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}

theorem exists_open_span_le {J : Type} [Fintype J] (a b : J → J → Ω) {z : M.Z}
    (h : Submodule.span (M.O z) (Set.range a) ≤ Submodule.span (M.O z) (Set.range b)) :
    ∃ V : M.Z.Opens, z ∈ V ∧ ∀ w ∈ V, Submodule.span (M.O w) (Set.range a) ≤ Submodule.span (M.O w) (Set.range b) := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  refine ⟨⟨⋂ i, ⋂ l, {w | (c i l : Ω) ∈ M.O w}, isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun l =>
    M.isOpen_setOf_mem_O _⟩, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun l => (c i l).2, fun w hw => ?_⟩
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (Submodule.mem_span_range_iff_exists_fun _).2
    ⟨fun l => ⟨c i l, Set.mem_iInter.1 (Set.mem_iInter.1 hw i) l⟩, hc i⟩

theorem exists_affine_basis {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) (B : Matrix J J Ω) {z : M.Z}
    (h : EE.E z = Submodule.span (M.O z) (Set.range B)) :
    ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ ∀ w ∈ W, EE.E w = Submodule.span (M.O w) (Set.range B) := by
  obtain ⟨U, b, hz, -, H⟩ := EE.loc z
  have e := (H z hz).symm.trans h
  obtain ⟨V₁, h₁, H₁⟩ := exists_open_span_le b B e.le
  obtain ⟨V₂, h₂, H₂⟩ := exists_open_span_le B b e.ge
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U ⊓ V₁ ⊓ V₂) (x := z) ⟨⟨hz, h₁⟩, h₂⟩
  exact ⟨W, hW, hzW, fun w hw => (H w (hle hw).1.1).trans (le_antisymm (H₁ w (hle hw).1.2) (H₂ w (hle hw).2))⟩

variable {K : Type} [Field K]

theorem range_subset {p : Sp K ⟶ M.Z} {U : M.Z.Opens} (h : p (IsLocalRing.closedPoint K) ∈ U) :
    Set.range p ⊆ U := by
  rw [range_eq_singleton p (IsLocalRing.closedPoint K), Set.singleton_subset_iff]
  exact h

theorem exists_point {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty)
    (ψ : M.ringOn U →+* K) :
    ∃ p : Sp K ⟶ M.Z, p (IsLocalRing.closedPoint K) ∈ U ∧ ∀ a : M.ringOn U, M.val p a = ψ a := by
  let χ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (ψ.comp (M.sectionsEquiv U hne).toRingHom)
  have h := le_preimage_specMap_fromSpec hU χ
  refine ⟨Spec.map χ ≫ hU.fromSpec, (le_preimage_iff _ _).1 h, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := (M.sectionsEquiv U hne).surjective a
  rw [coe_sectionsEquiv, val_valF ((top_le_preimage_iff _ _).1 h), valF_eq_valR, valR_eq _ _ h,
    valMap_specMap_fromSpec]
  rfl

theorem ext_of_val {U : M.Z.Opens} (hU : IsAffineOpen U) {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U)
    (H : ∀ a ∈ M.ringOn U, M.val p a = M.val q a) : p = q := by
  refine ext_of_valR hU ((le_preimage_iff _ _).2 hp) ((le_preimage_iff _ _).2 hq) fun g => ?_
  have := H _ ((mem_ringOn_iff_exists ⟨_, hp⟩).2 ⟨g, rfl⟩)
  rwa [val_valF (range_subset hp), val_valF (range_subset hq)] at this

theorem val_eq_of_adjoin {U : M.Z.Opens} {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U) {T : Set Ω}
    (hT : M.ringOn U = Algebra.adjoin F T) (h0 : ∀ a, M.val p (algebraMap F Ω a) = M.val q (algebraMap F Ω a))
    (h1 : ∀ a ∈ T, M.val p a = M.val q a) : ∀ a ∈ M.ringOn U, M.val p a = M.val q a := by
  have sp := specializes_of_range_eq (range_eq_singleton p (IsLocalRing.closedPoint K))
  have sq := specializes_of_range_eq (range_eq_singleton q (IsLocalRing.closedPoint K))
  intro a ha
  rw [hT] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h1 x hx
  | algebraMap r => exact h0 r
  | add x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_add sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_add sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]
  | mul x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_mul sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_mul sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]

theorem exists_ringHom (R : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) (S : Subalgebra F Ω')
    {T : Set Ω'} (hS : S = Algebra.adjoin F (φ '' (R : Set Ω) ∪ T)) (hT : ∀ y ∈ T, y = 1 ∨ y ∈ Set.range t)
    (v : R →+* K) (c : σ → K) :
    ∃ ψ : S →+* K, (∀ (r : R) (h : φ r ∈ S), ψ ⟨φ r, h⟩ = v r) ∧ ∀ j (h : t j ∈ S), ψ ⟨t j, h⟩ = c j := by
  let g : MvPolynomial σ R →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp R.val.toRingHom) t
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro P hP
    have := ht (MvPolynomial.map R.val.toRingHom P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact MvPolynomial.map_injective R.val.toRingHom Subtype.val_injective (this.trans (map_zero _).symm)
  have hC : ∀ r : R, g (MvPolynomial.C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ r
  have hX : ∀ j, g (MvPolynomial.X j) = t j := fun j => MvPolynomial.eval₂Hom_X' _ _ j
  have hle : ∀ y ∈ S, y ∈ g.range := by
    intro y hy
    rw [hS] at hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨r, hr, rfl⟩ | hx
      · exact ⟨_, hC ⟨r, hr⟩⟩
      · rcases hT x hx with rfl | ⟨j, rfl⟩
        · exact one_mem _
        · exact ⟨_, hX j⟩
    | algebraMap r => exact ⟨_, (hC (algebraMap F R r)).trans (φ.commutes r)⟩
    | add x y _ _ ex ey => exact add_mem ex ey
    | mul x y _ _ ex ey => exact mul_mem ex ey
  let e : MvPolynomial σ R ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩
  let ι : S →+* g.range := S.val.toRingHom.codRestrict g.range fun y => hle y y.2
  have key : ∀ (P : MvPolynomial σ R) (y : S), g P = y → e.symm (ι y) = P := fun P y h =>
    e.symm_apply_eq.2 (Subtype.ext h.symm)
  refine ⟨(MvPolynomial.eval₂Hom v c).comp (e.symm.toRingHom.comp ι), fun r h => ?_, fun j h => ?_⟩
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hC r))).trans (MvPolynomial.eval₂Hom_C _ _ r)
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hX j))).trans (MvPolynomial.eval₂Hom_X' _ _ j)

theorem div_of_ne_zero {J : Type} {t : J → Ω} {p : Sp K ⟶ M.Z} {c : J → K} {i k : J} (hi : c i ≠ 0)
    (hk : M.Div t k (p (IsLocalRing.closedPoint K))) (h : ∀ j, c j = c k * M.val p (t j / t k)) :
    M.Div t i (p (IsLocalRing.closedPoint K)) ∧ ∀ j, M.val p (t j / t i) = c j / c i := by
  have hr := range_eq_singleton p (IsLocalRing.closedPoint K)
  have h0 : M.val p (t i / t k) ≠ 0 := right_ne_zero_of_mul (h i ▸ hi)
  have hd : M.Div t i (p (IsLocalRing.closedPoint K)) :=
    (hk.div_iff_isUnit i).2 ((val_ne_zero_iff hr ⟨_, hk.2 i⟩).1 h0)
  refine ⟨hd, fun j => ?_⟩
  have e := val_mul (specializes_of_range_eq hr) (hd.2 j) (hk.2 i)
  rw [div_mul_div_cancel₀ hd.1] at e
  rw [eq_div_iff hi, h j, h i, e]
  ring

theorem projPoints {J : Type} [Fintype J] [DecidableEq J] {EE : M.Lat J} {s : J → Ω'}
    (H : ProjBundle M EE M' φ f s) : ProjPoints M EE M' φ f s := by
  refine ⟨H.hom, fun z' B _ hB => ?_, fun K _ x B hB hE c hc => ?_⟩
  · obtain ⟨W, hW, hz, hE⟩ := exists_affine_basis EE B hB
    exact (H.chart W B hW ⟨_, hz⟩ hE).1 z' hz
  obtain ⟨W, hW, hz, hEW⟩ := exists_affine_basis EE B hE
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  replace hi : c i ≠ 0 := hi
  obtain ⟨hti, hind⟩ := H.gen B hB i
  obtain ⟨U, hU, hUeq, hR⟩ := (H.chart W B hW ⟨_, hz⟩ hEW).2 i hti
  set t := (B.map φ).mulVec s with ht
  have hmem : ∀ z', z' ∈ U ↔ f z' ∈ W ∧ M'.Div t i z' := fun z' => Set.ext_iff.1 hUeq z'
  have hne : (U : Set M'.Z).Nonempty := by
    refine ⟨genericPoint M'.Z, (hmem _).2 ⟨?_, div_genericPoint hti⟩⟩
    rw [← M'.pt_apply (IsLocalRing.closedPoint Ω')]
    have e : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ∈ W := by
      rw [H.hom]
      exact M.top_le_preimage_pt ⟨_, hz⟩ (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    exact e
  let v : M.ringOn W →+* K := (valHom x _ (range_eq_singleton x (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (ringOn_le_O hz)).toRingHom
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_ringHom (M.ringOn W) _ hind (M'.ringOn U) hR (by
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · exact Or.inl (by rw [hj]; exact div_self hti)
    · exact Or.inr ⟨⟨j, hj⟩, rfl⟩) v fun j => c j.1 / c i
  obtain ⟨p, hp, hv⟩ := exists_point hU hne ψ
  have hφ : ∀ a ∈ M.ringOn W, φ a ∈ M'.ringOn U := fun a ha =>
    hR ▸ Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩)
  have hcomp : ∀ q : Sp K ⟶ M'.Z, q (IsLocalRing.closedPoint K) ∈ U → ∀ a ∈ M.ringOn W,
      M.val (q ≫ f) a = M'.val q (φ a) := fun q hq a ha =>
    H.hom.val_comp q _ (ringOn_le_O ((hmem _).1 hq).1 ha)
  have hpf : p ≫ f = x := by
    refine ext_of_val hW ((hmem _).1 hp).1 hz fun a ha => ?_
    exact (hcomp p hp a ha).trans ((hv ⟨_, hφ a ha⟩).trans (hψ₁ ⟨a, ha⟩ _))
  have hrat : ∀ j, M'.val p (t j / t i) = c j / c i := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hti, div_self hi, RatModel.val_one]
    · have hm : t j / t i ∈ M'.ringOn U := hR ▸ Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      exact (hv ⟨_, hm⟩).trans (hψ₂ ⟨j, hj⟩ hm)
  refine ⟨p, ⟨hpf, i, ((hmem _).1 hp).2, fun j => by rw [hrat, mul_div_cancel₀ _ hi]⟩, ?_⟩
  rintro q ⟨hqf, k, hk, hq⟩
  obtain ⟨hd, hqr⟩ := div_of_ne_zero hi hk hq
  have hqU : q (IsLocalRing.closedPoint K) ∈ U := (hmem _).2 ⟨by rw [← hqf] at hz; exact hz, hd⟩
  have hb : ∀ a ∈ M.ringOn W, M'.val q (φ a) = M'.val p (φ a) := fun a ha => by
    rw [← hcomp q hqU a ha, ← hcomp p hp a ha, hqf, hpf]
  refine ext_of_val hU hqU hp (val_eq_of_adjoin hqU hp hR (fun a => ?_) ?_)
  · rw [← φ.commutes]
    exact hb _ (Subalgebra.algebraMap_mem _ a)
  · rintro _ (⟨a, ha, rfl⟩ | ⟨j, rfl⟩)
    · exact hb a ha
    · exact (hqr j).trans (hrat j).symm

end GlobalTheory.FlagBundle.ProjPts

theorem GlobalTheory.FlagBundle.projPoints_of_projBundle : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω']
    [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J]
    [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H => GlobalTheory.FlagBundle.ProjPts.projPoints H

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExt
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocIntegral

open Polynomial
open scoped WithZero

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem exists_valued_eq (γ : ℤᵐ⁰) : ∃ c : v.adicCompletion K, Valued.v c = γ := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K γ
  exact ⟨algebraMap K _ x, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx⟩

theorem valued_coeff_minpoly_le_one (e : ℕ) (he : 0 < e)
    (f : v.adicCompletion K →+* v'.adicCompletion L)
    (hfv : ∀ y, Valued.v (f y) = Valued.v y ^ e) :
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ x : v'.adicCompletion L, Valued.v x ≤ 1 →
      ∀ n, Valued.v ((minpoly (v.adicCompletion K) x).coeff n) ≤ 1 := by
  letI := f.toAlgebra
  intro hfd x hx n
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ ℤᵐ⁰
  haveI : IsUltrametricDist (v.adicCompletion K) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion K)
      (Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰).toDist)
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  choose c hc using (exists_valued_eq (v := v) : ∀ γ : ℤᵐ⁰, ∃ c : v.adicCompletion K, Valued.v c = γ)
  have hmono : ∀ a b : v.adicCompletion K, Valued.v a ≤ Valued.v b → ‖a‖ ≤ ‖b‖ :=
    fun a b h => Valued.toNormedField.norm_le_iff.2 h
  have hnorm : ∀ a b : v.adicCompletion K, Valued.v a = Valued.v b → ‖a‖ = ‖b‖ :=
    fun a b h => le_antisymm (hmono a b h.le) (hmono b a h.ge)
  have he' : (e : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast he.ne')
  let ρ : v'.adicCompletion L → ℝ := fun z => ‖c (Valued.v z)‖ ^ ((e : ℝ)⁻¹)
  have ρ_nonneg : ∀ z, 0 ≤ ρ z := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have ρ_mul : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    simp only [ρ]
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul]
    congr 1
    apply hnorm
    rw [hc, Valuation.map_mul, Valuation.map_mul, hc, hc]
  have ρ_le : ∀ a b, Valued.v a ≤ Valued.v b → ρ a ≤ ρ b := by
    intro a b h
    exact Real.rpow_le_rpow (norm_nonneg _) (hmono _ _ (by rw [hc, hc]; exact h))
      (inv_nonneg.2 (Nat.cast_nonneg _))
  have ρ_zero : ρ 0 = 0 := by
    simp only [ρ]
    have : c (Valued.v (0 : v'.adicCompletion L)) = 0 := by
      rw [← Valuation.zero_iff Valued.v, hc, Valuation.map_zero]
    rw [this, norm_zero, Real.zero_rpow he']
  have ρ_eq_zero : ∀ z, ρ z = 0 → z = 0 := by
    intro z hz
    simp only [ρ] at hz
    rw [Real.rpow_eq_zero (norm_nonneg _) he', norm_eq_zero] at hz
    have := hc (Valued.v z)
    rw [hz, Valuation.map_zero] at this
    exact (Valuation.zero_iff _).1 this.symm
  have ρ_f : ∀ a, ρ (f a) = ‖a‖ := by
    intro a
    simp only [ρ]
    rw [hnorm _ (a ^ e) (by rw [hc, hfv, Valuation.map_pow]), norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) he.ne']
  have ρ_one : ρ 1 = 1 := by
    have := ρ_f 1
    rwa [map_one, norm_one] at this
  let N : AlgebraNorm (v.adicCompletion K) (v'.adicCompletion L) :=
    { toFun := ρ
      map_zero' := ρ_zero
      add_le' := fun a b => by
        rcases le_total (Valued.v a) (Valued.v b) with h | h
        · have := ρ_le (a + b) b ((Valuation.map_add _ a b).trans (max_le h le_rfl))
          linarith [ρ_nonneg a]
        · have := ρ_le (a + b) a ((Valuation.map_add _ a b).trans (max_le le_rfl h))
          linarith [ρ_nonneg b]
      neg' := fun a => by simp only [ρ, Valuation.map_neg]
      mul_le' := fun a b => (ρ_mul a b).le
      eq_zero_of_map_eq_zero' := ρ_eq_zero
      smul' := fun a z => by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ρ_mul, ρ_f] }
  have hN : ∀ z, N z = ρ z := fun _ => rfl
  have hpm : IsPowMul N := by
    intro a k hk
    clear hk
    rw [hN, hN]
    induction k with
    | zero => simp [ρ_one]
    | succ k ih => rw [pow_succ, ρ_mul, ih, pow_succ]
  have hu := spectralNorm_unique (K := v.adicCompletion K) (L := v'.adicCompletion L) hpm
  have hsx : spectralNorm (v.adicCompletion K) (v'.adicCompletion L) x ≤ 1 := by
    rw [← spectralAlgNorm_def, ← hu, hN, ← ρ_one]
    exact ρ_le x 1 (by rw [Valuation.map_one]; exact hx)
  have hxi : IsIntegral (v.adicCompletion K) x := Algebra.IsIntegral.isIntegral x
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hxi)] at hsx
  exact Valued.toNormedField.norm_le_one_iff.1 (hsx n)

end GlobalTheory.LocIntegral

namespace GlobalTheory.LocIntegral

open Polynomial

theorem isIntegral_iff_isIntegral_map : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ)
    (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e →
    (∀ y, Valued.v (f y) = Valued.v y ^ e) →
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ b₀ : Kbar v ≃+* Kbar v',
      (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) =
        algebraMap (v'.adicCompletion L) (Kbar v') (f x)) →
      ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔
        IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  intro K L _ _ _ _ v v' e f he hfv
  letI := f.toAlgebra
  intro hfd b₀ hb y
  have hle : ∀ a ∈ v.adicCompletionIntegers K, f a ∈ v'.adicCompletionIntegers L := by
    intro a ha
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hfv]
    exact pow_le_one₀ zero_le' ha
  let g : v.adicCompletionIntegers K →+* v'.adicCompletionIntegers L :=
    f.restrict (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) hle
  have hg : ∀ a, ((g a : v'.adicCompletionIntegers L) : v'.adicCompletion L) = f a := fun _ => rfl
  have hcomp : (algebraMap (v'.adicCompletionIntegers L) (Kbar v')).comp g =
      b₀.toRingHom.comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
      IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers L) (v'.adicCompletion L) (Kbar v'),
      hb]
    rfl
  constructor
  · intro hy
    exact IsIntegral.map_of_comp_eq g b₀.toRingHom hcomp hy
  · intro hy
    letI alg1 : Algebra (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := g.toAlgebra
    letI alg2 : Algebra (v'.adicCompletionIntegers L) (Kbar v) :=
      (b₀.symm.toRingHom.comp (algebraMap (v'.adicCompletionIntegers L) (Kbar v'))).toAlgebra
    haveI : IsScalarTower (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) (Kbar v) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      have h := congrArg (fun φ => b₀.symm (φ a)) hcomp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
      rw [← h]
      rfl
    haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := by
      constructor
      intro a
      have ha : Valued.v (a : v'.adicCompletion L) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2
      have hc := valued_coeff_minpoly_le_one e he f hfv hfd (a : v'.adicCompletion L) ha
      have hai : IsIntegral (v.adicCompletion K) (a : v'.adicCompletion L) :=
        Algebra.IsIntegral.isIntegral _
      have hl : minpoly (v.adicCompletion K) (a : v'.adicCompletion L) ∈
          Polynomial.lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc n)⟩, rfl⟩
      obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hai)
      refine ⟨q, hm, ?_⟩
      apply Subtype.ext
      have e1 := Polynomial.hom_eval₂ q (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L))
        (v'.adicCompletionIntegers L).subtype a
      have e2 : ((v'.adicCompletionIntegers L).subtype).comp
          (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L)) =
          (algebraMap (v.adicCompletion K) (v'.adicCompletion L)).comp
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        ext; rfl
      rw [e2, ← Polynomial.eval₂_map, hq] at e1
      exact e1.trans (minpoly.aeval (v.adicCompletion K) (a : v'.adicCompletion L))
    have h1 : IsIntegral (v'.adicCompletionIntegers L) y := by
      have := IsIntegral.map_of_comp_eq (RingHom.id (v'.adicCompletionIntegers L)) b₀.symm.toRingHom
        (by ext; rfl) hy
      simpa using this
    exact isIntegral_trans y h1

end GlobalTheory.LocIntegral
end
end

