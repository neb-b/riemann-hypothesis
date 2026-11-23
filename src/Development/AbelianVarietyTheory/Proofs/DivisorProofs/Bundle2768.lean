module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystem
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.LevelPrimePower

theorem iterate_fixes {A : Type} [CommGroup A] (f : A →* A) (ℓ : ℕ) (hf : ∀ x, x ^ ℓ = 1 → f x = x) (e : ℕ) :
    ∀ x : A, x ^ ℓ ^ (e + 1) = 1 → f^[ℓ ^ e] x = x := by
  induction e with
  | zero => intro x hx; simpa using hf x (by simpa using hx)
  | succ e ih =>
    intro x hx
    let h : A →* A := ((show Monoid.End A from f) ^ ℓ ^ e : Monoid.End A)
    have hh : ∀ a, h a = f^[ℓ ^ e] a := fun a => congrFun (Monoid.End.coe_pow A f _) a
    have h1 : h x ^ ℓ = x ^ ℓ := by
      rw [← map_pow, hh]
      exact ih _ (by rw [← pow_mul, ← pow_succ', hx])
    have hy : (h x / x) ^ ℓ = 1 := by rw [div_pow, h1, div_self']
    have h2 : h (h x / x) = h x / x := by
      rw [hh]
      exact ih _ (by rw [pow_succ', pow_mul, hy, one_pow])
    have h3 : ∀ n : ℕ, h^[n] x = x * (h x / x) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ihn =>
        rw [Function.iterate_succ_apply', ihn, map_mul, map_pow, h2, pow_succ', ← _root_.mul_assoc,
          mul_div_cancel]
    have h4 : (h : A → A) = f^[ℓ ^ e] := funext hh
    rw [pow_succ, Function.iterate_mul, ← h4, h3, hy, _root_.mul_one]

theorem exists_normal {G A : Type} [Group G] [CommGroup A] (ρ : G → A →* A) (h1 : ∀ x, ρ 1 x = x)
    (hm : ∀ σ τ x, ρ (σ * τ) x = ρ σ (ρ τ x)) (ℓ e : ℕ) (hf : ∀ σ x, x ^ ℓ = 1 → ρ σ x = x) :
    ∃ H : Subgroup G, H.Normal ∧ (∀ σ, σ ^ ℓ ^ e ∈ H) ∧ ∀ σ ∈ H, ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x := by
  let H : Subgroup G :=
    { carrier := {σ | ∀ x, x ^ ℓ ^ e = 1 → ρ σ x = x}
      one_mem' := fun x _ => h1 x
      mul_mem' := fun {a b} ha hb x hx => by rw [hm, hb x hx, ha x hx]
      inv_mem' := fun {a} ha x hx => by
        conv_lhs => rw [← ha x hx, ← hm, inv_mul_cancel, h1] }
  refine ⟨H, ⟨fun a ha g x hx => ?_⟩, fun σ x hx => ?_, fun σ hσ => hσ⟩
  · rw [hm, hm, ha _ (by rw [← map_pow, hx, map_one]), ← hm, mul_inv_cancel, h1]
  · have hp : ∀ (n : ℕ) x, ρ (σ ^ n) x = (ρ σ)^[n] x := by
      intro n
      induction n with
      | zero => intro x; simpa using h1 x
      | succ n ih => intro x; rw [pow_succ, hm, ih, Function.iterate_succ_apply]
    rw [hp]
    exact iterate_fixes _ ℓ (hf σ) e x (by rw [pow_succ, pow_mul, hx, one_pow])

theorem exists_factor_fixedField {F L : Type} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {Y : Scheme.{0}} (y : Sp L ⟶ Y) (h : ∀ σ ∈ H, spMap σ.toAlgHom.toRingHom ≫ y = y) :
    ∃ z : Sp (IntermediateField.fixedField H) ⟶ Y, spMap (algebraMap (IntermediateField.fixedField H) L) ≫ z = y := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective y
  have hy : (Scheme.SpecToEquivOfField L Y).symm ⟨p, φ⟩ = Spec.map φ ≫ Y.fromSpecResidueField p := rfl
  rw [hy] at h ⊢
  have hmem : ∀ b, φ.hom b ∈ IntermediateField.fixedField H := by
    intro b
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := h σ hσ
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp, Spec.map_inj] at h1
    exact congrArg (fun ψ => ψ.hom b) h1
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict (IntermediateField.fixedField H) hmem)) ≫
    Y.fromSpecResidueField p, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_intermediate {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {S : Scheme.{0}} (X : Over S) [GrpObj X] [IsCommMonObj X] (s₀ : Sp F ⟶ S) (s : Sp L ⟶ S)
    (hs : s = spMap (algebraMap F L) ≫ s₀) (ℓ e : ℕ) (hℓ : ℓ.Prime) (ζ₀ : F) (hζ : IsPrimitiveRoot ζ₀ ℓ)
    (hfix : ∀ z : Over.mk s ⟶ X, z ^ ℓ = 1 → ∃ w : Sp F ⟶ X.left, spMap (algebraMap F L) ≫ w = z.left) :
    ∃ M : IntermediateField F L, IsGalois F M ∧ (∃ d, Module.finrank F M = ℓ ^ d) ∧
      (∀ u : Lˣ, u ^ ℓ ^ e = 1 → (u : L) ∈ M) ∧
      ∀ z : Over.mk s ⟶ X, z ^ ℓ ^ e = 1 → ∃ w : Sp M ⟶ X.left, spMap (algebraMap M L) ≫ w = z.left := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hσ : ∀ σ : L ≃ₐ[F] L, spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap F L) = spMap (algebraMap F L) := by
    intro σ
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a
  let t : (L ≃ₐ[F] L) → (Over.mk s ⟶ Over.mk s) := fun σ => Over.homMk (spMap σ.toAlgHom.toRingHom) (by
    show spMap σ.toAlgHom.toRingHom ≫ s = s
    rw [hs, ← Category.assoc, hσ])
  let ρ : (L ≃ₐ[F] L) → (Over.mk s ⟶ X) →* (Over.mk s ⟶ X) := fun σ =>
    { toFun := fun x => t σ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  have hρ : ∀ σ x, (ρ σ x).left = spMap σ.toAlgHom.toRingHom ≫ x.left := fun _ _ => rfl
  obtain ⟨H₁, n₁, p₁, f₁⟩ := exists_normal ρ
    (fun x => Over.OverMorphism.ext (by
      rw [hρ]
      exact (congrArg (· ≫ x.left) (Spec.map_id (CommRingCat.of L))).trans (Category.id_comp _)))
    (fun σ τ x => Over.OverMorphism.ext (by
      rw [hρ, hρ, hρ]
      erw [← Category.assoc, ← Spec.map_comp]
      rfl)) ℓ e
    (fun σ x hx => Over.OverMorphism.ext (by
      obtain ⟨w, hw⟩ := hfix x hx
      rw [hρ, ← hw]
      erw [← Category.assoc, hσ]))
  obtain ⟨H₂, n₂, p₂, f₂⟩ := exists_normal (fun σ : L ≃ₐ[F] L => Units.map σ.toAlgHom.toRingHom.toMonoidHom)
    (fun x => rfl) (fun σ τ x => rfl) ℓ e
    (fun σ x hx => Units.ext (by
      have hx' : (x : L) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
      obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap F L).injective).eq_pow_of_pow_eq_one hx'
      show σ (x : L) = x
      rw [← hi, ← map_pow, σ.commutes]))
  let H := H₁ ⊓ H₂
  haveI : H.Normal := inferInstanceAs (H₁ ⊓ H₂).Normal
  have hP : IsPGroup ℓ ((L ≃ₐ[F] L) ⧸ H) := by
    intro g
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p₁ σ, p₂ σ⟩
  refine ⟨IntermediateField.fixedField H, inferInstance, ?_, fun u hu => ?_, fun z hz => ?_⟩
  · obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hP
    refine ⟨d, ?_⟩
    rw [← hd, ← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
  · rw [IntermediateField.mem_fixedField_iff]
    exact fun σ hσ => congrArg Units.val (f₂ σ hσ.2 u hu)
  · exact exists_factor_fixedField H _ fun σ hσ => congrArg CommaMorphism.left (f₁ σ hσ.1 z hz)

theorem exists_level_primePower : ∀ {Ω₁ : Type} [Field Ω₁] [CharZero Ω₁] {R₁ : Type} [CommRing R₁] (emb : R₁ →+* Ω₁) (P₁ : PolAV (Sp R₁)) (ℓ M K : ℕ), ℓ.Prime → 0 < M → ℓ ∣ M → (∃ e, K = ℓ ^ e) → (∃ ζ₀ : Ω₁, IsPrimitiveRoot ζ₀ M) → (∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp R₁) (z : Over.mk x ⟶ P₁.A), z ^ M = 1 → ∃ y : baseOver (Sp R₁) ⟶ P₁.A, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₁)) ≫ y = z) → ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra Ω₁ Ω₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (ζ : Ω₂ˣ), FiniteDimensional Ω₁ Ω₂ ∧ IsGalois Ω₁ Ω₂ ∧ (∃ e, Module.finrank Ω₁ Ω₂ = ℓ ^ e) ∧ IsPrimitiveRoot ζ K ∧ Q.g = P₁.g ∧ IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp emb)) φ ∧ LBIso Q.L (P₁.L.pull φ) ∧ Nonempty (Out.Level Q K (unitOn ζ)) := by
  intro F _ _ R₁ _ emb P₁ ℓ N K hℓ hN hℓN ⟨e, hK⟩ ⟨ζ₀, hζ₀⟩ hsec
  have hK0 : 0 < K := hK ▸ pow_pos hℓ.pos e
  have := P₁.isAb.comm
  obtain ⟨L, _, _, Q₃, φ₃, ζ₃, hfd, hgal, hζ₃, -, h₃, -, ⟨lev⟩⟩ := LevelGalois.exists_level_galois emb P₁ K hK0
  obtain ⟨c, rfl⟩ := hℓN
  have hζ₁ : IsPrimitiveRoot (ζ₀ ^ c) ℓ := hζ₀.pow hN (Nat.mul_comm _ _)
  have hs : spMap ((algebraMap F L).comp emb) = spMap (algebraMap F L) ≫ spMap emb := (GlobalTheory.spMap_comp_spMap _ _).symm
  obtain ⟨M, hMgal, hdeg, hroot, hpts⟩ := exists_intermediate P₁.A (spMap emb) (spMap ((algebraMap F L).comp emb)) hs
    ℓ e hℓ _ hζ₁ (fun z hz => by
      let τ := algebraMap L (AlgebraicClosure L)
      let k : Over.mk (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ⟶ Over.mk (spMap ((algebraMap F L).comp emb)) :=
        Over.homMk (spMap τ) rfl
      obtain ⟨y, hy⟩ := hsec _ _ (k ≫ z) (by rw [← MonObj.comp_pow, pow_mul, hz, one_pow, MonObj.comp_one])
      exact ⟨spMap emb ≫ y.left, (cancel_epi (spMap τ)).1 (by
        have hy' : (spMap τ ≫ spMap ((algebraMap F L).comp emb)) ≫ y.left = spMap τ ≫ z.left :=
          congrArg CommaMorphism.left hy
        rw [← hy', hs]
        simp only [Category.assoc])⟩)
  rw [← hK] at hroot hpts
  haveI : CharZero M := (algebraMap F M).charZero_iff (algebraMap F M).injective |>.1 inferInstance
  have hB := GlobalTheory.laws_without_cohomology.2.2.1
  let ζ' : M := ⟨ζ₃, hroot ζ₃ hζ₃.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' K :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap M L) (IsPrimitiveRoot.coe_units_iff.2 hζ₃)
      (algebraMap M L).injective
  obtain ⟨ζ, hζe⟩ := hζ'.isUnit hK0.ne'
  have hζ : IsPrimitiveRoot ζ K := IsPrimitiveRoot.coe_units_iff.1 (hζe ▸ hζ')
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre hB ((algebraMap F M).comp emb) P₁
  obtain ⟨Q', ψ, hQ'⟩ := exists_isPolFibre hB (algebraMap M (AlgebraicClosure M)) Q
  refine ⟨M, inferInstance, inferInstance, Q, φ, ζ, inferInstance, hMgal, hdeg, hζ, hQ.1, hQ.2.1, hQ.2.2.symm,
    LevelGalois.nonempty_level_of_rational Q K hK0 ζ hζ Q' ψ hQ' fun y hy => by
    let σ := algebraMap M (AlgebraicClosure M)
    let τ' : L →ₐ[M] AlgebraicClosure M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    let τ : L →+* AlgebraicClosure M := τ'.toRingHom
    have hτ : spMap τ ≫ spMap (algebraMap M L) = spMap σ := by
      rw [GlobalTheory.spMap_comp_spMap]
      exact congrArg spMap (RingHom.ext τ'.commutes)
    have hML : spMap (algebraMap M L) ≫ spMap ((algebraMap F M).comp emb) = spMap ((algebraMap F L).comp emb) := by
      rw [GlobalTheory.spMap_comp_spMap]
      rfl
    have hPg : IsGrpPullback Q.A P₁.A (spMap ((algebraMap F M).comp emb)) φ := hQ.2.1
    have hQg : IsGrpPullback Q'.A Q.A (spMap σ) ψ := hQ'.2.1
    let y₀ := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
    have hy₀ : y₀ ^ K = 1 := by simp only [y₀, ← map_pow, hy, map_one]
    let j : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
        Over.mk (((𝟙_ (Over (Sp (AlgebraicClosure M)))).hom ≫ spMap σ) ≫ spMap ((algebraMap F M).comp emb)) :=
      Over.homMk (𝟙 _) (by
        show 𝟙 _ ≫ (𝟙 _ ≫ spMap σ) ≫ _ = spMap τ ≫ _
        rw [Category.id_comp, Category.id_comp, ← hML, ← hτ, Category.assoc])
    let y₁ := j ≫ y₀
    have hy₁ : y₁ ^ K = 1 := by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one]
    have hy₁l : y₁.left = (y.left ≫ ψ) ≫ φ := Category.id_comp _
    let y₂ := (ObjPull.pushEquiv h₃ (Over.mk (spMap τ))).symm y₁
    obtain ⟨a, ha⟩ := lev.span _ (spMap τ) y₂ (by rw [← map_pow, hy₁, map_one])
    rw [← GenSpread.comp_linComb] at ha
    set v := linComb lev.pt (fun i => (a i : ℕ)) with hv
    have hvl : spMap τ ≫ v.left = y₂.left := congrArg CommaMorphism.left ha
    let z : Over.mk (spMap ((algebraMap F L).comp emb)) ⟶ P₁.A := Over.homMk (v.left ≫ φ₃) (by
      rw [Category.assoc, h₃.1.w, ← Category.assoc, Over.w v]
      exact Category.id_comp _)
    let k : Over.mk ((Over.mk (spMap τ)).hom ≫ spMap ((algebraMap F L).comp emb)) ⟶
        Over.mk (spMap ((algebraMap F L).comp emb)) := Over.homMk (spMap τ) rfl
    have hzl : spMap τ ≫ z.left = y₁.left := by
      rw [← ObjPull.pushEquiv_symm_left h₃ _ y₁]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ₃) hvl)
    have hkz : k ≫ z = y₁ := Over.OverMorphism.ext hzl
    have hz : z ^ K = 1 := by
      have h : k ≫ z ^ K = k ≫ 1 := by rw [MonObj.comp_pow, hkz, hy₁, MonObj.comp_one]
      exact Over.OverMorphism.ext ((cancel_epi (spMap τ)).1 (congrArg CommaMorphism.left h))
    obtain ⟨w, hw⟩ := hpts z hz
    have hw2 : w ≫ P₁.A.hom = 𝟙 _ ≫ spMap ((algebraMap F M).comp emb) := by
      refine (cancel_epi (spMap (algebraMap M L))).1 ?_
      rw [← Category.assoc, hw, Over.w z, Category.id_comp, hML]
      rfl
    let x : 𝟙_ (Over (Sp M)) ⟶ Q.A := Over.homMk (hPg.1.lift w (𝟙 _) hw2) (hPg.1.lift_snd _ _ _)
    have hxl : x.left ≫ φ = w := hPg.1.lift_fst _ _ _
    refine ⟨x, ?_⟩
    apply Over.OverMorphism.ext
    refine hQg.1.hom_ext ?_ ?_
    · rw [ObjPull.secPull_left]
      refine hPg.1.hom_ext ?_ ?_
      · rw [Category.assoc, hxl, ← hy₁l, ← hzl, ← hw, ← Category.assoc, hτ]
      · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
        exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rw [Over.w, Over.w]⟩

end GlobalTheory.LevelPrimePower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalLogCanonicalThresholdAtPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_threshold_lcAt_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (D B : X → ℚ) (x : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsQCart B → KltAt p n (Δ + D) x → ¬ KltAt p n (Δ + D + B) x → ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ LcAt p n (Δ + D + c • B) x ∧ ¬ KltAt p n (Δ + D + c • B) x := by
  intro hP X _ _ _ p n hp hn Δ m G D B x hm hG hD hB hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨mD, D₀, hmD, -, rfl⟩ := hD
  obtain ⟨m', B₀, hm', -, rfl⟩ := hB
  obtain ⟨η, hη, hG₁⟩ := isLogCanonicalMultiple_add_qWeil X p n Δ m mD G D₀ hm hmD hG
  have hm₁ : 0 < m * mD := Nat.mul_pos hm hmD
  obtain ⟨S, hSf, hS⟩ :=
    _root_.GlobalTheory.PairStep.finite_test_divisors hP X p n hp hn η (m * mD) (mD • G + m • D₀) B₀ hη hm₁
  obtain ⟨g, hg⟩ := (mD • G + m • D₀).exists_isEqn x
  obtain ⟨f, hf⟩ := B₀.exists_isEqn x
  have hL := hG₁ x g hg
  have hBf : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → qWeil B₀ m' z = (E.ord f : ℚ) / m' := by
    intro z hz E hE
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  obtain ⟨a, ha⟩ : ∃ a : DivOver p → ℚ, ∀ E, a E = discrep E η (m * mD) g := ⟨_, fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : DivOver p → ℚ, ∀ E, t E = (E.ord f : ℚ) / m' := ⟨_, fun _ => rfl⟩
  have hrw (c : ℚ) (E : DivOver p) :
      a E - c * t E = discrep E η (m * mD) g - c / m' * E.ord f := by
    rw [ha, ht]; ring
  have step (c : ℚ) : ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧
      IsLogEqn p (Δ + qWeil D₀ mD + c • qWeil B₀ m') η x m'' g'' ∧
      ∀ E : DivOver p, discrep E η m'' g'' = a E - c * t E := by
    obtain ⟨m'', g'', h1, h2, h3⟩ :=
      _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n (Δ + qWeil D₀ mD) (qWeil B₀ m') η x (m * mD) m' g f c hm₁ hm' hL hBf
    exact ⟨m'', g'', h1, h2, fun E => by rw [h3, ha, ht]⟩
  have hka : ∀ E : DivOver p, E.Through x → -1 < a E := fun E hE => by
    rw [ha]; exact (hL.kltAt_iff hn hη hm₁).1 hk E hE

  obtain ⟨E₀, hE₀S, hE₀x, hE₀⟩ : ∃ E ∈ S, E.Through x ∧ a E - 1 * t E ≤ -1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨m₁', g₁, hm₁', hL₁, hd₁⟩ := step 1
    rw [one_smul] at hL₁
    refine hnk ((hL₁.kltAt_iff hn hη hm₁').2 fun E hE => ?_)
    rw [hd₁, hrw]
    refine (hS x g f (1 / m') hg hf).1 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    exact hc E' hE' hE'x
  have hT0 : E₀ ∈ {E | E ∈ S ∧ E.Through x ∧ 0 < t E} :=
    ⟨hE₀S, hE₀x, by have := hka E₀ hE₀x; linarith⟩
  obtain ⟨E₁, ⟨hE₁S, hE₁x, hE₁t⟩, hmin⟩ :=
    Set.exists_min_image {E | E ∈ S ∧ E.Through x ∧ 0 < t E} (fun E => (1 + a E) / t E)
      (hSf.subset fun E hE => hE.1) ⟨E₀, hT0⟩
  have hE₁a := hka E₁ hE₁x
  refine ⟨(1 + a E₁) / t E₁, div_pos (by linarith) hE₁t, ?_, ?_⟩
  · refine (hmin E₀ hT0).trans ?_
    rw [div_le_one hT0.2.2]
    linarith
  obtain ⟨m'', g'', hm'', hL'', hd''⟩ := step ((1 + a E₁) / t E₁)
  refine ⟨(lcAt_iff_of_isLogEqn X p n hp hn _ η x m'' g'' hη hm'' hL'').2 fun E hE => ?_,
    fun hk' => ?_⟩
  · rw [hd'', hrw]
    refine (hS x g f ((1 + a E₁) / t E₁ / m') hg hf).2 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    by_cases htE : 0 < t E'
    · have := hmin E' ⟨hE', hE'x, htE⟩
      rw [le_div_iff₀ htE] at this
      linarith
    · have h0 : 0 ≤ (1 + a E₁) / t E₁ := (div_pos (by linarith) hE₁t).le
      have := hka E' hE'x
      nlinarith
  · have := (hL''.kltAt_iff hn hη hm'').1 hk' E₁ hE₁x
    rw [hd'', div_mul_cancel₀ _ hE₁t.ne'] at this
    linarith

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.GenRestrict

theorem exists_surjective_coordMap_equivMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (p : ℕ), p.Prime → (p : R) ∈ maximalIdeal R → ∀ (Wo : Set (Sp R)), IsOpen Wo → (∀ y, PsiUnitOn D.toPre y Wo) → (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) ∈ Wo → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∃ ρ : D.toPre.X →+ D'.toPre.X, Function.Surjective ρ ∧ CoordMap D.toPre D'.toPre g ρ ∧ EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hVd G' _ _ hG' D' A' U' g β p _ _ Wo hWo hψ hker gp hL
  obtain ⟨⟨hRN, -, -, hRA⟩, -⟩ := id hR
  obtain ⟨⟨-, -, hVI, -⟩, hV0⟩ := id hV
  obtain ⟨N, _, _, _, φ, g', hN, hφ, hg', hfac⟩ := GlobalTheory.FarTrait.exists_factor g
  obtain ⟨hNN, hNI, hNA, hN0⟩ := hN
  have hNb : GlobalTheory.Mum.Base N := ⟨⟨hNN, inferInstance, hNI, hNA⟩, hN0⟩
  have hsp : spMap g' ≫ spMap φ = spMap g := by
    rw [← Spec.map_comp]
    exact congrArg spMap (RingHom.ext hfac)
  have hgen : spMap φ (genericPoint (Sp N)) ∈ (⟨Wo, hWo⟩ : (Sp R).Opens) := by
    have e : spMap φ (genericPoint (Sp N)) = (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun r => ?_)
      change φ r ∈ (⊥ : Ideal N) ↔ r ∈ RingHom.ker g
      rw [Ideal.mem_bot, RingHom.mem_ker, ← hfac, map_eq_zero_iff g' hg']
    rw [e]
    exact hker
  have hG₂ : IsSemiAbelian ((Over.pullback (specOf φ)).obj G) := Geo.Tor.IsSemiAbelian.pullback _ G hG
  haveI : IsCommMonObj ((Over.pullback (specOf φ)).obj G) := hG₂.comm
  have hbc : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom :=
    inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (specOf φ)).obj G)))
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U N hNb.1 φ hφ ⟨Wo, hWo⟩ hψ hgen
    ((Over.pullback (specOf φ)).obj G) (Iso.refl _) hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U N hNb _ hG₂ D₂ A₂ U₂ φ (pullback.fst G.hom (specOf φ)) hφ
    (Iso.refl _) hbc (Category.id_comp _).symm hD hU
  have sq : β ≫ G.hom = (G'.hom ≫ spMap g') ≫ specOf φ := by
    rw [Category.assoc, gp.1.w, ← hsp]
  let β₂ : G'.left ⟶ ((Over.pullback (specOf φ)).obj G).left := pullback.lift β (G'.hom ≫ spMap g') sq
  have hβ : β₂ ≫ pullback.fst G.hom (specOf φ) = β := pullback.lift_fst _ _ _
  have hβ' : β₂ ≫ pullback.snd G.hom (specOf φ) = G'.hom ≫ spMap g' := pullback.lift_snd _ _ _
  have gp₂ : IsGrpPullback G' ((Over.pullback (specOf φ)).obj G) (spMap g') β₂ :=
    (isGrpPullback_pullback G (specOf φ)).cancel (gp.congr hsp.symm hβ.symm) hβ'
  have hL₂ : LBIso U'.LG.L (U₂.LG.L.pull β₂) :=
    LBIso.trans U'.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hL
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ β₂ hβ.symm).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂
  have hs := GlobalTheory.TorusOntoSpread.restrict_surjective N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂ ρ hρ
  have hT := GlobalTheory.SpreadTorMatch.torMatch_of_spread N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂ ρ hρ
  have hC₂ := TorCoord.coordMap_of_torMatch N hNb _ hG₂ D₂ A₂ U₂ V hV hVd G' hG' D' A' U' g' β₂ hg' gp₂ hL₂ ρ hT
  have hE₂ := equivMap_of_torMatch N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ hg' ρ hT
  refine ⟨ρ.comp hD.xe.symm.toAddMonoidHom, hs.comp hD.xe.symm.surjective, fun y r r' hr hr' => ?_,
    fun f f' hf hf' hff m m' hm hm' y => ?_⟩
  · obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm.toAddMonoidHom y)
    rw [← hfac]
    exact ((hC₁ y r r₂ hr hr₂).map g').trans (hC₂ _ r₂ r' hr₂ hr')
  · have hf₂ : IsMonHom ((Over.pullback (specOf φ)).map f) := inferInstance
    have e₁ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst G.hom (specOf φ) =
        pullback.fst G.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
    have e₂ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.snd G.hom (specOf φ) =
        pullback.snd G.hom (specOf φ) := Over.w ((Over.pullback (specOf φ)).map f)
    have e₃ : f'.left ≫ β₂ = β₂ ≫ ((Over.pullback (specOf φ)).map f).left := by
      refine pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        erw [e₁, hβ, ← Category.assoc, hβ, hff]
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        erw [e₂, hβ', ← Category.assoc, Over.w f']
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom N hNb _ hG₂ D₂ A₂ U₂ _ hf₂
    have h₁ := hE₁ f _ hf hf₂ e₁ m m₂ hm hm₂ y
    exact (congrArg ρ h₁).trans (hE₂ _ f' hf₂ hf' e₃ m₂ m' hm₂ hm' _)

end GlobalTheory.Poinc.Eq8.GenRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystemStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateSimilitude_heckeTranslate_latticeSystem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N) (fun g => (GlobalTheory.UPel.HT.Hecke.transl g.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = I.ev N y := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.TateTranslSys.exists_tateIsoO_transl_sys) | (exact GlobalTheory.UPel.HT.HeckeAd.TateTranslSys.exists_tateIsoO_transl_sys) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.TateTranslSys.exists_tateIsoO_transl_sys  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupPrimePowerLevelRegularChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem exists_setup_regAt_chart : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ l : ℕ, l.Prime → l ∣ n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), j₀ ≤ j ∧ X₁.S.r * X₁.S.N = (l ^ j) ^ 2 ∧ IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ev ∧ RegAt X₁ z₁ ev ∧ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧ Refines Q ρ D₀.toPre e₀ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hth V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU l hl hln j₀
  obtain ⟨j, Y, q, hj, hqf, hqs, hB⟩ := _root_.GlobalTheory.Poinc.SetupCov.exists_setup_cov g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hth l hl hln j₀
  obtain ⟨V₁, _, _, _, ρ, D₀, e₀, y, y', hcn, hinj, hfin, href, hy, hy'⟩ :=
    _root_.GlobalTheory.Poinc.Sep.SharpExt.exists_refined_ext_lift g n F Z i W hW V Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hqf hqs
  obtain ⟨X₁, yM, hrN, hyM, hreg⟩ := hB (FractionRing V₁) y'
  obtain ⟨z₁, ev, hloc, he1, he2⟩ := _root_.GlobalTheory.FiniteLift.exists_stalk_lift V₁ hcn.2.1 X₁.M.Z Z X₁.π X₁.fin (spMap ρ ≫ ξ) yM
    (by rw [hyM, ← Category.assoc, hy', hy])
  refine ⟨j, X₁, z₁, V₁, inferInstance, inferInstance, inferInstance, ρ, ev, D₀, e₀, hj, hrN, hcn, hinj, hfin, hloc, ?_, he1,
    href⟩
  intro a ha
  rw [he2]
  exact hreg a ha

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpli
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

theorem GlobalTheory.TorCls.centraliser_at_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c :=
  fun p _ G β hβ y₀ c hc => GlobalTheory.TorCls.AtP.atp_of_bijective G (GlobalTheory.T.padicPoints_similitude_GL_product_bijective p G) β hβ y₀ c hc
end

