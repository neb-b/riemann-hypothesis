module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegLatticeNumberFieldExtensionEq
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.BarEqOfLamEqMultiplier
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem bar_eq_of_lamEq_multiplier : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (P B : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A) (f : P.A ⟶ B.A) (h : 𝓞 E), 1 ≤ P.g → (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → LamEq B.L f f P.L (act.act h) (𝟙 P.A) → H.bar h = h := by
  intro hL E _ _ _ H K _ _ P B act f h hg hadj hf
  have : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have : IsCommMonObj P.A := P.isAb.comm
  have : IsCommMonObj B.A := B.isAb.comm
  have c := GlobalTheory.LamCalc.lamEq_calculus (Sp (𝓞 K)) P.A P.A

  have h₁ : LamEq B.L f f P.L (𝟙 P.A) (act.act h) :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hf).2.1
  have h₂ : LamEq P.L (𝟙 P.A) (act.act h) B.L f f :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 h₁).1
  have h₃ : LamEq B.L f f P.L (𝟙 P.A) (act.act (H.bar h)) :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) _ _).2.1 hf).2.2.1 (hadj h)
  have h₄ : LamEq P.L (𝟙 P.A) (act.act h) P.L (𝟙 P.A) (act.act (H.bar h)) :=
    ((c P.A B.A P.A P.L B.L P.L P.isLB B.isLB P.isLB _ (𝟙 _) _ (𝟙 _) f f f f _ _).2.1 h₂).2.2.1 h₃
  have h₅ : LamEq P.L (act.act h) (𝟙 P.A) P.L (act.act (H.bar h)) (𝟙 P.A) :=
    ((c P.A P.A P.A P.L P.L P.L P.isLB P.isLB P.isLB _ (𝟙 _) _ (𝟙 _) _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 h₄).2.1
  exact (_root_.GlobalTheory.LamF.Faithful.act_injective hL E K P act hg (_root_.GlobalTheory.CM.PairingInj.eq_of_lamEq hL _ P _ _ _ h₅)).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmHostRootNegDiscriminantNeNegSelf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHost_rootNegDiscriminant_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have : (H.d : ℂ) = 0 := by simpa using h2.symm
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem cmHost_rootNegDiscriminant_ne_neg_self (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  apply cmHost_rootNegDiscriminant_ne_zero H
  linear_combination h / 2

theorem cmHost_conj_sqrtNegDisc (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h2 := H.sqrt_neg_disc_sq
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp [pow_two] at him hre
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem host_emb_rt_sq (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
  have h := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  rw [H.sqrt_neg_disc_sq]
  simpa using h

theorem host_mem_compl_psiSet (H : Host E) (τ : E →+* ℂ) :
    τ ∈ (psiSet H)ᶜ ↔ τ (H.rt : E) = -H.rt0 := by
  change ¬ (τ (H.rt : E) = H.rt0) ↔ _
  constructor
  · intro h
    exact (sq_eq_sq_iff_eq_or_eq_neg.1 (host_emb_rt_sq H τ)).resolve_left h
  · intro h h'
    exact cmHost_rootNegDiscriminant_ne_neg_self H (h'.symm.trans h)

theorem card_psiSet_eq_card_compl (H : Host E) :
    Nat.card (psiSet H) = Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) := by
  refine Nat.card_congr
    { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, ?_⟩
      left_inv := fun τ => Subtype.ext (star_star τ.1)
      right_inv := fun τ => Subtype.ext (star_star τ.1) }
  · rw [host_mem_compl_psiSet, ComplexEmbedding.conjugate_coe_eq, ← cmHost_conj_sqrtNegDisc]
    exact congrArg _ τ.2
  · have h := (host_mem_compl_psiSet H τ.1).1 τ.2
    change _ = H.rt0
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, cmHost_conj_sqrtNegDisc, neg_neg]

theorem card_psiSet (H : Host E) : Nat.card (psiSet H) = Module.finrank ℚ E / 2 := by
  have h1 := Set.ncard_add_ncard_compl (psiSet H)
  have h2 := card_psiSet_eq_card_compl H
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
  rw [Nat.card_eq_fintype_card, Embeddings.card E ℂ] at h1
  rw [Nat.card_coe_set_eq]
  omega

variable {H : Host E} {l : Level H}

theorem labK_eq_iff (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (τ : E →+* ℂ) (a : E) (x : c.F) :
    labK c K τ a = algebraMap c.F K x ↔ τ a = (x : ℂ) := by
  change algebraMap c.F K (Formalism.L2.Pj.embF c τ a) = _ ↔ _
  rw [(algebraMap c.F K).injective.eq_iff, Subtype.ext_iff]
  rfl

theorem labK_injective (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] : Function.Injective (labK c K) := by
  intro τ τ' h
  refine RingHom.ext fun a => ?_
  exact (labK_eq_iff c K τ a (Formalism.L2.Pj.embF c τ' a)).1 (DFunLike.congr_fun h a)

theorem labK_bijective (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] :
    Function.Bijective (labK c K) := by
  have : Finite (E →+* K) := Finite.of_equiv _ (RingHom.equivRatAlgHom E K).symm
  refine (labK_injective c K).bijective_of_nat_card_le ?_
  rw [Nat.card_eq_fintype_card (α := E →+* ℂ), Embeddings.card E ℂ]
  exact card_ringHom_le_finrank

end

theorem labK_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K], Function.Bijective (labK c K) ∧ Splits E K ∧ (∀ τ, ∃ t : 𝓞 E →+* 𝓞 K, ∀ a : 𝓞 E, (t a : K) = labK c K τ (a : E)) ∧ ∃ ρ : 𝓞 K, ρ ^ 2 = -(H.d : 𝓞 K) ∧ (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) ∧ (∀ τ, τ ∈ (psiSet H)ᶜ ↔ labK c K τ (H.rt : E) = ((-ρ : 𝓞 K) : K)) ∧ Nat.card (psiSet H) = Module.finrank ℚ E / 2 ∧ Nat.card ((psiSet H)ᶜ : Set (E →+* ℂ)) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H l c K _ _ _
  have hb := labK_bijective c K
  refine ⟨hb, ?_, fun τ => ⟨RingOfIntegers.mapRingHom (labK c K τ), fun a => rfl⟩, ?_⟩
  · rw [splits_iff_card, ← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Embeddings.card E ℂ]
  let r : c.F := ⟨H.rt0, c.le (baseKA l).ρ.2⟩
  have hr : r ^ 2 = -(H.d : c.F) := Subtype.ext (by simpa [r] using H.sqrt_neg_disc_sq)
  have hK : (algebraMap c.F K r) ^ 2 = -(H.d : K) := by
    rw [← map_pow, hr]; simp
  have hint : IsIntegral ℤ (algebraMap c.F K r) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hK]
    exact (isIntegral_natCast H.d).neg
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 K, algebraMap (𝓞 K) K ρ = algebraMap c.F K r := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨ρ, RingOfIntegers.ext ?_, fun τ => ?_, fun τ => ?_, card_psiSet H, ?_⟩
  · change algebraMap (𝓞 K) K (_ ^ 2) = algebraMap (𝓞 K) K (-_)
    rw [map_pow, map_neg, map_natCast, hρ]
    exact hK
  · change _ ↔ _ = algebraMap (𝓞 K) K ρ
    rw [hρ]
    exact (labK_eq_iff c K τ _ r).symm
  · rw [host_mem_compl_psiSet]
    have := (labK_eq_iff c K τ (H.rt : E) (-r)).symm
    rw [map_neg, ← hρ, ← map_neg] at this
    exact this
  · rw [← card_psiSet_eq_card_compl, card_psiSet]

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEqNdegOfLine
section
open NumberField ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM

namespace GlobalTheory.LamF

theorem deg_eq_ndeg_of_line : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (Λ : Submodule (𝓞 K) V) (v : V) (ℓ : MLine K),
    v ≠ 0 → ℓ.Good → (∀ z, z ∈ Λ ↔ ∃ c ∈ ℓ.I, z = c • v) → (∀ s, ℓ.n s ^ 2 = (h.form s v v).re) →
    deg h Λ = ℓ.ndeg := by
  intro K _ _ V _ _ _ _ h Λ v ℓ hv hℓ hΛ hn
  rw [GlobalTheory.CM.deg_ideal_smul h Λ hv (m := fun s => ℓ.n s ^ 2) (fun s => pow_pos (hℓ.2 s) 2)
    (fun s => (hn s).symm) hℓ.1 (fun z => (hΛ z).trans ⟨fun ⟨c, a, b⟩ => ⟨c, b, a⟩, fun ⟨c, a, b⟩ => ⟨c, b, a⟩⟩),
    MLine.ndeg, MLine.deg, meanLog]
  simp only [Real.log_pow, ← Finset.mul_sum, Nat.cast_ofNat]
  ring

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegLatticeNumberFieldExtensionEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_lattice_numberField_extension_eq : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ) (h : HermFam K (Fin n → K)) (h' : HermFam K' (Fin n → K')) (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → (∀ s a b, h'.form s (Pi.single a 1) (Pi.single b 1) = h.form (s.comp j) (Pi.single a 1) (Pi.single b 1)) → deg h' (Submodule.span (𝓞 K') ((fun c i => j (c i)) '' (Λ : Set (Fin n → K)))) = deg h Λ := by
  first | exact @GlobalTheory.deg_span_image_eq | exact GlobalTheory.deg_span_image_eq | (intros; apply GlobalTheory.deg_span_image_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section

namespace GlobalTheory.LamF.Ind

open GlobalTheory.SqZero GlobalTheory.LieComb

section General

variable {R : Type} [CommRing R] {S : Scheme.{0}} (f : Sp R ⟶ S)

def scaleOver (c : R) : Over.mk ((epsR R).hom ≫ f) ⟶ Over.mk ((epsR R).hom ≫ f) :=
  (Over.map f).map (Chart.spMap (epsTo R (TrivSqZeroExt.inr c : DualNumber R)
    (TrivSqZeroExt.inr_mul_inr _ _ _)) : epsR R ⟶ epsR R)

variable {f} {G : Over S} {G' : Over (Sp R)} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  [IsCommMonObj G'] {φ : G'.left ⟶ G.left}

theorem push_tanExp (Φ : (epsR R ⟶ G') ≃* (Over.mk ((epsR R).hom ≫ f) ⟶ G))
    (hΦ : ∀ x, (Φ x).left = x.left ≫ φ) {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (c : Fin n → R) :
    Φ (tanExp v c) = ∏ i, scaleOver f (c i) ≫ Φ (v i) := by
  refine (map_prod Φ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  apply Over.OverMorphism.ext
  rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc]
  rfl

theorem prod_comp {T G₁ : Over S} [GrpObj G₁] [IsCommMonObj G₁] (F : G ⟶ G₁) [IsMonHom F]
    {J : Type} (s : Finset J) (x : J → (T ⟶ G)) : (∏ i ∈ s, x i) ≫ F = ∏ i ∈ s, x i ≫ F :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ G => y ≫ F) fun a b => MonObj.mul_comp a b F) x s


omit [GrpObj G] [IsCommMonObj G] in
theorem eq_zero_of_pow {K : Type} [Field K] [CharZero K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] {n : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v) {c : Fin n → K}
    {N : ℕ} (hN : 0 < N) (h : tanExp v c ^ N = 1) : c = 0 := by
  have h₁ : tanExp v (N • c) = tanExp v 0 := by
    change (combHom hv.1 (N • c)).toMul = (combHom hv.1 0).toMul
    rw [map_nsmul, map_zero, toMul_nsmul]
    exact h
  have h₂ := (isLieBasisOver_self hv).1 _ _ h₁
  funext i
  have := congrFun h₂ i
  simpa [hN.ne'] using this

end General

theorem lamInd : LamIndSt := by
  intro E _ _ _ _ H l cf _ nΨ n' f o La hg L hL hdet
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, ⟨hmΨ, hm', N, ψΨ, ψ', hN, -, hsum⟩, -⟩ := hg
  obtain ⟨hsrc, -, hw, -⟩ := hL
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  choose w hw hwc using hw
  obtain ⟨ΦB, hΦB⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hB.1 (epsR o.K₁)
  obtain ⟨ΦΨ, hΦΨ⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ hΨ.1 (epsR o.K₁)
  obtain ⟨Φ', hΦ'⟩ := exists_mulEquiv_points_of_isGrpPullback _ _ _ _ _ _ h'.1 (epsR o.K₁)
  let e := Equiv.ofBijective _ hsrc
  have he : ∀ q, L.src (e.symm q) = q := fun q => e.apply_symm_apply q
  have hwl : ∀ j i, ΦB (w (e.symm (.inl (j, i)))) = ΦΨ (o.xΨ.v i) ≫ o.φΨ j := fun j i => by
    have := hw (e.symm (.inl (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦΨ, Category.assoc]
    exact this
  have hwr : ∀ j i, ΦB (w (e.symm (.inr (j, i)))) = Φ' (o.x'.v i) ≫ o.φ' j := fun j i => by
    have := hw (e.symm (.inr (j, i)))
    rw [LamLetters.IsLetter, he] at this
    apply Over.OverMorphism.ext
    rw [hΦB, Over.comp_left, hΦ', Category.assoc]
    exact this
  have hone : tanExp w c = 1 := by
    obtain rfl : w = fun k => tanExp o.xB.v (L.U k) :=
      funext fun k => (isLieComb_iff_tanExp _ _).1 (hwc k)
    refine (tanExp_tanExp o.xB.basis.1 (fun k => L.U k) c).trans ?_
    rw [← Matrix.vecMul_eq_sum, hc]
    exact lieExp_eq_one o.xB.basis.1 _ (fun _ => rfl) _
  have hpad : ∀ a b : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A,
      padd _ a b = a * b := fun _ _ => rfl
  have hps : ∀ (n : ℕ) (f : Fin n → (Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ o.B.A)),
      psumPt f = (List.ofFn f).prod := by
    intro n f
    rw [List.prod_eq_foldr]
    rfl
  have hpow : ∀ (G : Over (Sp (𝓞 o.K₁))) [GrpObj G] (n : ℕ)
      (a : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ G), pnsmulPt n a = a ^ n := by
    intro G _ n a
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  let a := fun j => ΦΨ (tanExp o.xΨ.v fun i => c (e.symm (.inl (j, i))))
  let a' := fun j => Φ' (tanExp o.x'.v fun i => c (e.symm (.inr (j, i))))
  have hs : padd o.B.A (psumPt fun k => a k ≫ o.φΨ k) (psumPt fun k => a' k ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, ← map_one ΦB, ← hone,
      push_tanExp ΦB hΦB, ← e.symm.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type,
      Fintype.prod_prod_type]
    congr 1 <;> refine Finset.prod_congr rfl fun j _ => ?_
    · have := hmΨ j
      simp only [a, push_tanExp ΦΨ hΦΨ, prod_comp, hwl, Category.assoc]
    · have := hm' j
      simp only [a', push_tanExp Φ' hΦ', prod_comp, hwr, Category.assoc]
  have hs₀ : padd o.B.A
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φΨ k)
      (psumPt fun k => (1 : Over.mk ((epsR o.K₁).hom ≫ gmap o.K₁) ⟶ _) ≫ o.φ' k) = 1 := by
    rw [hpad, hps, hps, List.prod_ofFn, List.prod_ofFn, Finset.prod_eq_one, Finset.prod_eq_one,
      _root_.mul_one]
    · intro j _
      have := hm' j
      exact MonObj.one_comp _
    · intro j _
      have := hmΨ j
      exact MonObj.one_comp _
  obtain ⟨p₁, p₂⟩ := hsum _ a a'
  obtain ⟨q₁, q₂⟩ := hsum _ (fun _ => 1) (fun _ => 1)
  rw [hs] at p₁ p₂
  rw [hs₀] at q₁ q₂
  apply hc0
  funext k
  obtain ⟨q, rfl⟩ := e.symm.surjective k
  rcases q with ⟨j, i⟩ | ⟨j, i⟩
  · have h := (p₁ j).symm.trans (q₁ j)
    rw [hpow _, hpow _, one_pow,
      ← map_pow, map_eq_one_iff _ ΦΨ.injective] at h
    exact congrFun (eq_zero_of_pow o.xΨ.basis hN h) i
  · have h := (p₂ j).symm.trans (q₂ j)
    rw [hpow _, hpow _, one_pow,
      ← map_pow, map_eq_one_iff _ Φ'.injective] at h
    exact congrFun (eq_zero_of_pow o.x'.basis hN h) i

end GlobalTheory.LamF.Ind
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EvalFrEqProdDetPowMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

noncomputable def blockDetPoly (K : Type) [CommRing K] {B : Type} (m : B → ℕ) (b : B) :
    MvPolynomial (FrVar m) K :=
  (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det

theorem evalFr_map_blockDetPoly {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S) :
    evalFr (MvPolynomial.map φ (blockDetPoly K m b)) X = (X b).det := by
  unfold evalFr blockDetPoly
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i k
  simp

theorem evalFr_blockDetPoly {K : Type} [CommRing K] {B : Type}
    [Fintype B] (m : B → ℕ) (b : B) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) :
    evalFr (blockDetPoly K m b) X = (X b).det := by
  have := evalFr_map_blockDetPoly (RingHom.id K) m b X
  rwa [MvPolynomial.map_id] at this

theorem exists_eq_prod_blockDetPoly_pow_mul (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B]
    [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (s : ℕ) :
    ∀ (n : B → ℕ), ∑ b, n b = s → ∀ (P : MvPolynomial (FrVar m) K),
      (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K),
        (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
        evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + n b)) * evalFr P X) →
      ∃ G : MvPolynomial (FrVar m) K, P = (∏ b, blockDetPoly K m b ^ n b) * G := by
  induction s with
  | zero =>
    intro n hn P _
    have h0 : ∀ b, n b = 0 := fun b =>
      (Finset.sum_eq_zero_iff.1 hn) b (Finset.mem_univ b)
    exact ⟨P, by simp [h0]⟩
  | succ s ih =>
    intro n hn P hP
    obtain ⟨b₀, -, hb₀⟩ : ∃ b ∈ (Finset.univ : Finset B), n b ≠ 0 :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega)
    obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.FrameDet.det_dvd_of_equivariant K B m P (fun b i => a b i + n b) hP b₀ (fun i => by omega)
    change P = blockDetPoly K m b₀ * Q at hQ
    set n' : B → ℕ := Function.update n b₀ (n b₀ - 1) with hn'
    have hn'0 : n' b₀ + 1 = n b₀ := by simp only [hn', Function.update_self]; omega
    have hn'1 : ∀ b, b ≠ b₀ → n' b = n b := fun b hb => by
      simp only [hn', Function.update_of_ne hb]
    have hsum : ∑ b, n' b = s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀)] at hn ⊢
      have : ∑ b ∈ Finset.univ.erase b₀, n' b = ∑ b ∈ Finset.univ.erase b₀, n b :=
        Finset.sum_congr rfl fun b hb => hn'1 b (Finset.ne_of_mem_erase hb)
      omega
    have hev : ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
        evalFr P X = (X b₀).det * evalFr Q X := fun X => by
      rw [← evalFr_blockDetPoly m b₀ X, hQ]
      simp only [evalFr, map_mul]
    obtain ⟨G, hG⟩ := ih n' hsum Q (by
      intro X b t hX ht htri
      have h := hP X b t hX ht htri
      rw [hev, hev] at h
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self, Matrix.det_mul] at h
        have hd : t.det = ∏ i, t i i := Matrix.det_of_upperTriangular htri
        have hp : (∏ i, t i i ^ (a b i + n b)) = t.det * ∏ i, t i i ^ (a b i + n' b) := by
          rw [hd, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← hn'0]; ring
        rw [hp] at h
        apply mul_left_cancel₀ (mul_ne_zero (hX b) ht)
        rw [h]; ring
      · rw [Function.update_of_ne (Ne.symm hb)] at h
        rw [hn'1 b hb]
        apply mul_left_cancel₀ (hX b₀)
        rw [h]; ring)
    refine ⟨G, ?_⟩
    rw [hQ, hG, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b₀),
      ← Finset.mul_prod_erase _ (fun b => blockDetPoly K m b ^ n b) (Finset.mem_univ b₀)]
    have : ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n' b
        = ∏ b ∈ Finset.univ.erase b₀, blockDetPoly K m b ^ n b :=
      Finset.prod_congr rfl fun b hb => by rw [hn'1 b (Finset.ne_of_mem_erase hb)]
    rw [this, ← hn'0]; ring

theorem evalFr_eq_prod_det_pow_mul : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (N : ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i + N)) * evalFr P X) → ∃ G : MvPolynomial (FrVar m) K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S), evalFr (MvPolynomial.map φ P) X = (∏ b, (X b).det) ^ N * evalFr (MvPolynomial.map φ G) X := by
  intro K _ _ B _ _ m P a N hP
  obtain ⟨G, hG⟩ := exists_eq_prod_blockDetPoly_pow_mul K B m a _ (fun _ => N) rfl P hP
  refine ⟨G, fun S _ φ X => ?_⟩
  rw [hG, ← Finset.prod_pow]
  simp only [← evalFr_map_blockDetPoly φ m _ X]
  simp only [evalFr, map_mul, map_prod, map_pow]

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealLocalGenOfValuation
section
open NumberField IsDedekindDomain Formalism.L2.LamCM
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_isLocGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K]
    (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  intro K _ _ oa hfin
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ oa v, ?_, fun p a ha => ?_⟩
  · refine finprod_induction (fun L : FractionalIdeal (𝓞 K)⁰ K => L ≠ 0) one_ne_zero
      (fun _ _ h h' => mul_ne_zero h h') fun v => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  · rw [isLocGen_iff_valuation_eq, FractionalIdeal.count_finprod K p oa, ha]
    exact hfin

end GlobalTheory.LamF
end

