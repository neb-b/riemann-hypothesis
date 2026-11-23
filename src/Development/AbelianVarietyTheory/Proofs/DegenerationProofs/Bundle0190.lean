module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightLeAddOfTorsionPairing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScale
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.ThetaBound

theorem le_of_sum {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨T, hT⟩ := h q
  have := v.map_le_add (hT T le_rfl) (v.map_le_sum (s := T) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem square_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hϖ : Irreducible ϖ)
    (hQ : QForm.IsQ D.toPre ϖ Q) (n : ℕ) (hn : 1 ≤ n) (y χ : D.toPre.X) :
    (0 : ℚ) ≤ 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 := by
  have h0 : 0 ≤ Q (n • χ + y) := by
    by_cases h : n • χ + y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ h)
  have e : Q (n • χ + y) = n ^ 2 * Q χ + n * QForm.bOf D.toPre Q y χ + Q y := by
    have e₁ : Q (n • χ + y) = Q (n • χ) + Q y + QForm.bOf D.toPre Q (n • χ) y := by
      simp only [QForm.bOf]; ring
    have e₂ : QForm.bOf D.toPre Q χ y = QForm.bOf D.toPre Q y χ := by
      simp only [QForm.bOf, add_comm χ y]; ring
    rw [e₁, DVR.Q_nsmul hϖ hQ, DVR.bOf_nsmul_left hϖ hQ, e₂]; ring
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 : (0 : ℚ) ≤ (n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y := by
    rw [e] at h0; exact_mod_cast h0
  have e₃ : 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 =
      ((n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y) / (n : ℚ) ^ 2 := by
    field_simp
    push_cast
    ring
  rw [e₃]
  positivity

theorem norm_theta_le : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  intro hL hL₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x rig e th s _ hS ϖ Q v lam hϖ hv hN w₀ th' ϑ c hW hE hP hc a
  obtain ⟨-, htf, hth, -⟩ := hS
  obtain ⟨-, hQ, -, hle, -⟩ := hN
  obtain ⟨hLL, h₁, h₂, h₃, h₄⟩ := laws_all hL hL₂
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hn : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (le_trans one_le_two S.N_ge)
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn
  obtain ⟨q, hq⟩ := hsurj (x a) (htf a).1
  have hqx := (hf q (x a)).2 hq.symm
  obtain ⟨-, hmul, huniq, hex⟩ := GlobalTheory.TestFibre.CombValue.valIs_linear hL u.V u.A (PadicAlgCl p) 1 (x a) (e a)
  obtain ⟨c', hc'⟩ := hex (htf a).2.1 th'
  have hval : y₀ ⟨S.th a, S.th_mem a⟩ = c * c' := huniq th _ _ (hth a) (hmul th' th c c' hc hc')
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv
    u.A u.G u.semi u.U w₀ rig hW (S.r * S.N) hn q (x a) hqx (e a) (htf a)
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv q.g
  have hsv := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ th' ϑ c' hE hc'
  have h0 : ((0 : ℚ) : WithTop ℚ) ≤ v c' := le_of_sum hsv fun χ =>
    le_trans (WithTop.coe_le_coe.2 (square_nonneg hϖ hQ (S.r * S.N) hn q.y χ))
      ((hterm 1 le_rfl w₁ ϑ hw₁).2 _ _ 0 (hqk _ hn q) hv₁ hP.1 χ)
  have h1 : ‖c'‖ ≤ 1 := by simpa using (hle c' 0).1 h0
  rw [hval, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.ThetaBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemistableOfRationalLTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem iter_lift {R K Ω : Type} [CommRing R] [Field K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
    (I : Ideal R) (φ : Ω ≃ₐ[K] Ω) (q : ℕ)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ q ∈ I) (n : ℕ) (x : R) :
    ∃ y : R, algebraMap R Ω y = (φ ^ n) (algebraMap R Ω x) ∧ y - x ^ (q ^ n) ∈ I := by
  induction n with
  | zero => exact ⟨x, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hI⟩ := ih
    obtain ⟨z, hz, hJ⟩ := h y
    refine ⟨z, by rw [hz, hy, pow_succ', AlgEquiv.mul_apply], ?_⟩
    rw [← Ideal.Quotient.eq] at hI hJ ⊢
    rw [hJ, map_pow, hI, ← map_pow, ← pow_mul, pow_succ]

theorem pow_pow_fixed {k : Type} [Monoid k] (c : k) (a : ℕ) (h : c ^ a = c) (n : ℕ) : c ^ (a ^ n) = c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_lift_frac {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (g : A →+* L) (hg : Function.Injective g) : ∃ j : K →+* L, j.comp (algebraMap A K) = g :=
  ⟨IsFractionRing.lift hg, RingHom.ext fun a => IsFractionRing.lift_algebraMap hg a⟩

theorem isSemiAbelian_of_rational_torsion (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l)
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left)
    (W L R K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra V W] [Algebra K L] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K'] [Algebra R K'] [IsFractionRing R K']
    [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω] [IsLocalHom (algebraMap W R)]
    (hWR : Function.Injective (algebraMap W R)) (hRΩ : Function.Injective (algebraMap R Ω))
    (hcW : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hVΩ : (algebraMap W Ω).comp (algebraMap V W) = (algebraMap K Ω).comp (algebraMap V K))
    (hk : IsAlgClosed (IsLocalRing.ResidueField R)) (hlR : IsUnit (l : R))
    (p r₀ f : ℕ) (hp : p.Prime) (hpR : CharP (IsLocalRing.ResidueField R) p) (hr₀ : 1 ≤ r₀) (hf : 1 ≤ f)
    (hres : ∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r₀) ^ m) = c)
    (σ φ : Ω ≃ₐ[K] Ω) (hfix : ∀ w : W, (φ ^ f) (algebraMap W Ω w) = algebraMap W Ω w)
    (hφ : ∀ x : R, ∃ y : R, algebraMap R Ω y = φ (algebraMap R Ω x) ∧ y - x ^ (p ^ r₀) ∈ IsLocalRing.maximalIdeal R)
    (hζ : ∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ (p ^ r₀))
    (hL : ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L,
      φ (σ x) = (σ ^ (p ^ r₀)) (φ x) ∧ (σ x = x → ∃ a b : R, algebraMap R Ω b ≠ 0 ∧ x * algebraMap R Ω b = algebraMap R Ω a))
    (G : Over (Sp W)) [GrpObj G] (hG : SmConn G) (hmod : IsModel (L := L) P.A G)
    (hdim : SmoothOfRelativeDimension P.g G.hom)
    (N : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left)
    (hN : AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) N)
    (c : ℕ) (hc : 1 ≤ c)
    (hext : ∀ y : Over.mk (spMap ((algebraMap R K').comp (algebraMap W R))) ⟶ G, ∃ s : Sp R ⟶ G.left,
      s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R K') ≫ s = (y ^ c).left) :
    IsSemiAbelian G := by
  classical
  obtain ⟨j', hj0⟩ := exists_lift_frac (K := K') (algebraMap R Ω) hRΩ
  have hj' : ∀ x : R, j' (algebraMap R K' x) = algebraMap R Ω x := fun x => RingHom.congr_fun hj0 x
  obtain ⟨i, hi⟩ := exists_lift_frac (K := L) ((algebraMap R K').comp (algebraMap W R))
    ((IsFractionRing.injective R K').comp hWR)
  replace hi := hi.symm
  have hjW : (j'.comp i).comp (algebraMap W L) = algebraMap W Ω := by
    rw [RingHom.comp_assoc, ← hi]
    exact RingHom.ext fun w => (hj' _).trans (IsScalarTower.algebraMap_apply W R Ω w).symm
  have hjK : (j'.comp i).comp (algebraMap K L) = algebraMap K Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) ?_
    rw [RingHom.comp_assoc, ← hcW, ← RingHom.comp_assoc, hjW, hVΩ]
  obtain ⟨θ, hθ, hθK⟩ := GlobalTheory.T.grpScheme_points_model_over_field K W L P.A G hmod Ω (j'.comp i) hjK hjW
  obtain ⟨e, act, hact, he, hpair, hrel, hdef⟩ := _root_.GlobalTheory.SS.galois_action_torsion_points K P Ω l (p ^ r₀) hl htors σ φ K' j' hζ
    (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
      obtain ⟨a, b, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
      refine ⟨algebraMap R _ a / algebraMap R _ b, ?_⟩
      rw [map_div₀, hj', hj', div_eq_iff hb0]
      exact hab.symm⟩)
  have hcard := (_root_.GlobalTheory.torsion_points_galois_module K P Ω l hl).1
  haveI := P.isAb.comm
  have hψ : (φ ^ f).toRingEquiv.toRingHom.comp (j'.comp i) = j'.comp i := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors W) ?_
    rw [RingHom.comp_assoc, hjW]
    exact RingHom.ext fun w => hfix w
  obtain ⟨t, a, m, C, Q, H, U, hm, hH, hcnt, hQ, hU, hHU, hT⟩ :=
    _root_.GlobalTheory.SS.frobenius_on_integral_torsion W R Ω hRΩ hk p (r₀ * f) l hp hpR (Nat.mul_pos hr₀ hf) hl hlR
      (fun c => by
        obtain ⟨m, hm, h⟩ := hres c
        refine ⟨m, hm, ?_⟩
        rw [pow_mul, ← pow_mul _ f m, mul_comm f m, pow_mul _ m f]
        exact pow_pow_fixed c _ h f)
      (φ ^ f).toRingEquiv.toRingHom (fun w => hfix w)
      (fun x => by rw [pow_mul]; exact iter_lift _ φ _ hφ f x)
      G hG P.g hdim N hN (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) θ (act (φ ^ f))
      (fun x => hθ _ hψ _ _ (hact _ x))
  rw [← map_pow, ← pow_mul] at hU hHU
  have hqq : (p ^ (r₀ * f)) ^ m = (p ^ r₀) ^ (f * m) := by rw [pow_mul, ← pow_mul _ f m]
  rw [hqq] at hU hQ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hg : P.g ≤ t + a := by
    refine _root_.GlobalTheory.SS.Weight.le_add_of_torsion (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) Ω l ((p ^ r₀) ^ (f * m)) P.g t a c C hl h3
      (Nat.cast_ne_zero.2 hl.ne_zero) ?_ hc hcard e he (act σ) (act (φ ^ (f * m))) (hpair _) (hrel _)
      (fun x hx => Over.OverMorphism.ext ((hact σ x).trans (htors σ x hx))) H U Q ?_ hcnt hQ hU hHU
    · rw [← pow_mul]
      exact Nat.one_lt_pow (Nat.mul_pos hr₀ (Nat.mul_pos hf hm)).ne' hp.one_lt
    · intro n x hx hS
      obtain ⟨y, hy⟩ := hdef n x hx hS
      obtain ⟨y', hy'⟩ := hθK K' i j' rfl x y hy _ hi
      obtain ⟨s, hs₁, hs₂⟩ := hext y'
      refine (hH _).2 ⟨s, hs₁, ?_⟩
      rw [← hy', ← hs₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj0]
  have hproper : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
    obtain ⟨ε, -⟩ := hmod
    haveI := P.isAb.proper
    rw [← Over.w ε.hom]
    have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj P.A).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    have : IsIso ε.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ε.hom))
    infer_instance
  · clear hcard
    refine _root_.GlobalTheory.SS.isSemiAbelian_of_proper_generic_of_torusExtension W L G hG hproper _ _ ?_ ?_ (hT hg)
    · ext w
      rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
    · intro z
      obtain ⟨m, hm, h⟩ := hres z
      have h1 : 1 < (p ^ r₀) ^ m := by
        rw [← pow_mul]
        exact Nat.one_lt_pow (Nat.mul_pos hr₀ hm).ne' hp.one_lt
      refine ⟨Polynomial.X ^ ((p ^ r₀) ^ m) - Polynomial.X, ?_, by simp [h]⟩
      refine Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow _) ?_
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast h1

theorem potentialSemistable_rational_lTorsion_any_closure (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (IsLocalRing.ResidueField V)) (l : ℕ) (hl : l.Prime) (h3 : 3 ≤ l) (hlu : IsUnit (l : V))
    (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω]
    (htors : ∀ (τ : Ω ≃ₐ[K] Ω) (x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l = 1 →
      spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) :
    PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  classical
  obtain ⟨R, _, σ, φ, hSH, hloc, hres, hW, hσ, hφ, hζ, hL⟩ := _root_.GlobalTheory.SS.exists_maxUnramified_frobenius_tame V K hfin l hl hlu Ω _ rfl
  letI := Fintype.ofFinite (IsLocalRing.ResidueField V)
  obtain ⟨p, hpV⟩ := CharP.exists (IsLocalRing.ResidueField V)
  obtain ⟨r₀, hp, hq⟩ := FiniteField.card (IsLocalRing.ResidueField V) p
  rw [← Nat.card_eq_fintype_card] at hq
  rw [hq] at hres hφ hζ hL
  have hpR : CharP (IsLocalRing.ResidueField R) p :=
    charP_of_injective_ringHom (IsLocalRing.ResidueField.map (algebraMap V R)).injective p
  have hVΩ : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hRΩ : Function.Injective (algebraMap R Ω) := Subtype.val_injective
  have hVR : Function.Injective (algebraMap V R) := fun a b h => hVΩ (congrArg Subtype.val h)
  obtain ⟨K', _, _, hSH⟩ : ∃ (K' : Type) (_ : Field K') (_ : Algebra R K'), SH R K' := ⟨_, _, _, hSH⟩
  haveI : IsFractionRing R K' := hSH.2.2.2
  obtain ⟨jK, hjK'⟩ := exists_lift_frac (K := K) ((algebraMap R K').comp (algebraMap V R))
    ((IsFractionRing.injective R K').comp hVR)
  letI : Algebra K K' := jK.toAlgebra
  have hcomp : (algebraMap R K').comp (algebraMap V R) = (algebraMap K K').comp (algebraMap V K) := hjK'.symm
  obtain ⟨s, c, hc, hgeo⟩ := GlobalTheory.T.exists_neronNeutralComponent_finite_level V K R K' hSH hcomp P
  obtain ⟨W, hWd, hs, hWc, hWf, hWl, f, hf, hfix⟩ := hW s
  obtain ⟨G, _, L, _, _, _, _, hG, hcW, hmod, hdim, ⟨N, hN⟩, hext⟩ := hgeo W hWd hs hWl
  have hlR : IsUnit (l : R) := by simpa using hlu.map (algebraMap V R)
  haveI : IsLocalHom (algebraMap W R) := hWl
  have hsemi : IsSemiAbelian G :=
    isSemiAbelian_of_rational_torsion V K l hl h3 P Ω htors W L R K' Subtype.val_injective hRΩ hcW
      (IsScalarTower.algebraMap_eq V K Ω) hSH.2.2.1 hlR p r₀ f hp hpR r₀.2 hf hres σ φ (fun w => hfix w.1 w.2) hφ hζ
      (fun L h₁ h₂ h₃ x hx => ⟨(hL L h₁ h₂ h₃ x hx).1, fun h => by
        obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hL L h₁ h₂ h₃ x hx).2 h
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hab⟩⟩)
      G hG hmod hdim N hN c hc hext
  have hVW : IsLocalHom (algebraMap V W) := ⟨fun v hv => by
    have : IsUnit (algebraMap V R v) := hv.map W.val
    exact (isUnit_map_iff (algebraMap V R) v).1 this⟩
  exact ⟨W, L, inferInstance, inferInstance, hWd, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcW, hWf, hVW, hWc, G, inferInstance, hmod, hsemi⟩

theorem potModel_of_rational_torsion : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → 3 ≤ l → IsUnit (l : V) → ∀ (P : Out.PolAV (Sp K)), (∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ P.A), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hfin l hl h3 hlu P htors
  exact potentialSemistable_rational_lTorsion_any_closure V K hfin l hl h3 hlu P (AlgebraicClosure K) htors

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTrait
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Rig
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]

theorem rigidification_map_on_values (m : CubeMap A G) {L₀ : LB G.left} {L₁ : LB A.left} (w : LB.Iso L₁ (L₀.pull m.F))
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A) (fun _ => 1)) ρ₁ (m.rigPull L₀ ρ₀)) :
    IsRigidificationPullbackCompatibleIso w m.e ρ₁ ρ₀ := by
  have H := (maps_iff w _ (fun _ => eSec G) _ ρ₁ ρ₀ m.e _ (rigPull_le m.F m.e m.e_comm L₀) (fun _ => rfl)).1 h
  intro Z r z J J' hJ hJ'
  have e : (r ≫ m.e) ≫ eSec G = (r ≫ eSec A) ≫ m.F := by rw [Category.assoc, Category.assoc, m.e_comm]
  refine (val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ m.e) z J
    (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => congrArg J e)).trans ?_
  refine (H Z r z (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => J' (r ≫ eSec A)) (fun _ => hJ _) (fun _ => hJ' _)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  rfl

end Rig

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem mem_nonzeroLocus_iff_sv {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J} (hJ : Good L₁ z J) : r z ∈ nonzeroLocus s ↔ IsUnit (VVRank.sv A s r z J) := by
  have hz := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have hz' : r z ∈ (LPow A L₁ a T).U k := (T ⊗ A).left.basicOpen_le _ hk
    have hu := (MulFinite.isUnit_gs r z _ hz' _).2 hk
    have e := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z hz' hz
    exact isUnit_of_mul_isUnit_right (e ▸ hu :)
  · intro h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, (MulFinite.isUnit_gs r z _ hz _).1 h⟩

theorem SecRel.mem_nonzeroLocus (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {s : LB.Sec (LPow A L₁ a T)}
    {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀) (y : (T ⊗ A).left)
    (hy : psi hp τ hτ y ∈ nonzeroLocus s₀) : y ∈ nonzeroLocus s := by
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := (mem_nonzeroLocus_iff_sv s₀ (𝟙 _ ≫ psi hp τ hτ) y hJ).1 hy
  rw [h _ _ _ _ _ hJ hJ'] at q
  exact (mem_nonzeroLocus_iff_sv s (𝟙 _) y hJ').2 (isUnit_of_mul_isUnit_right q)

theorem SecRel.pullS {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (τ' : T'.left ⟶ T₀'.left) (hτ' : τ' ≫ T₀'.hom = T'.hom ≫ f) (ξ : T' ⟶ T)
    (ξ₀ : T₀' ⟶ T₀) (e : τ' ≫ ξ₀.left = ξ.left ≫ τ) :
    SecRel hp τ' hτ' w (VVRank.pullS A a ξ s) (VVRank.pullS G a ξ₀ s₀) := by
  intro Z r z J J' hJ hJ'
  have e' : psi hp τ' hτ' ≫ (ξ₀ ▷ G).left = (ξ ▷ A).left ≫ psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
        Category.assoc, Category.assoc, psi_fst', e, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, whiskerRight_fst]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
        VVRank.whisker_snd_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, VVRank.sv_pullS _ _ _ _ _ _ hJ', Category.assoc, e', ← Category.assoc,
    h _ _ _ _ _ hJ hJ', Category.assoc, VVRank.whisker_snd_left]


include hp hτ in
theorem exists_pt_down (x₀ : T₀ ⟶ G) {n : ℕ} (hn : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have hc : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc)
  have hx : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ hc).symm
  refine ⟨x, hx, Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩
  rw [← over_pow hp τ hτ hx n, hn, over_one hp τ hτ]


include hp hτ in
theorem exists_pt_up [IsIso τ] (x : T ⟶ A) {n : ℕ} (hn : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, Over.w_assoc, ← hτ, IsIso.inv_hom_id_assoc])
  have hx : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, hx, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

end Move

theorem theta_at_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hV E _ _ _ H S t V _ _ _ hC χ t' m P σ hσ
  obtain ⟨hD, hA, hZ⟩ := hC
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have hR : IsRigidificationPullbackCompatibleIso w χ t'.PP.rig t.PP.rig := by
    have q := rigidification_map_on_values m.cm w hr
    rw [m.base] at q
    exact q
  have hp := m.cart
  have hL₀ := t.PP.isLB
  have hL₁ := t'.PP.isLB
  let τ : (Over.mk (𝟙 (Sp V))).left ⟶ (Over.mk χ).left := 𝟙 (Sp V)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp V)))
  have hτ : τ ≫ (Over.mk χ).hom = (Over.mk (𝟙 (Sp V))).hom ≫ χ := rfl
  obtain ⟨σ', hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ σ
  have hσ' : NZ t'.G t'.PP.L (𝟙 (Sp V)) σ' := by
    obtain ⟨g, hg, hg'⟩ := hσ
    obtain ⟨κ, -, h₂⟩ := ThetaPtUp.exists_psi_inv' hp τ hτ
    have e : psi hp τ hτ (κ g) = g := congrArg (fun q => q g) h₂
    refine ⟨κ g, ?_, SecRel.mem_nonzeroLocus hp τ hτ hL₀ hL₁ hs _ (e.symm ▸ hg')⟩
    have e' := congrArg (fun q => q (κ g)) (psi_fst' hp τ hτ)
    exact e'.symm.trans ((congrArg (fst (Over.mk χ) t.G).left e).trans hg)
  have key : ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → IsGenSec t'.G t'.PP.L ((1 : ℕ) : ℤ) σ' ∧ ∀ n : ℕ, Odd n →
      IsUnit (n : V) → 3 ≤ n → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))),
      (∀ x (c : F), ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) → 0 ≤ v c) ∧
      ∃ x, ∃ c : F, ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) ∧ v c = 0 := by
    intro ϖ hϖ F _ _ _ v hv
    choose Q hQ using QForm.exists_QVal hϖ P.D
    have q := GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing hV V hA ϖ hϖ P.D Q hQ F v hv P.A t'.G t'.semi P.U
    dsimp only at q
    rw [P.bundle] at q
    exact q σ' hσ'
  refine ⟨?_, fun ϖ hϖ F _ _ _ v hv n h₁ h₂ h₃ x' ξ hξ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
    exact ThetaPtUp.isGenSec_up hp τ hτ hw hL₀ hL₁ hs (key ϖ hϖ _ v hv).1
  · let ξ' : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V)) :=
      Over.homMk (jFK (R := V) F ≫ jK V) (Category.comp_id _)
    obtain ⟨k₁, x, c, k₂, k₃⟩ := (key ϖ hϖ F v hv).2 n h₁ h₂ h₃ ξ'
    let τ' : (Over.mk (jFK (R := V) F ≫ jK V)).left ⟶ (Over.mk x').left := 𝟙 (Sp F)
    haveI : IsIso τ' := inferInstanceAs (IsIso (𝟙 (Sp F)))
    have hτ' : τ' ≫ (Over.mk x').hom = (Over.mk (jFK (R := V) F ≫ jK V)).hom ≫ χ :=
      (Category.id_comp _).trans ((Over.w ξ).symm.trans (congrArg (· ≫ χ) hξ))
    have hs' := SecRel.pullS hp τ hτ hs τ' hτ' ξ' ξ
      ((Category.id_comp _).trans (hξ.trans (Category.comp_id _).symm))
    have hi : inv τ' = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    refine ⟨fun y₀ d hd => ?_, ?_⟩
    · obtain ⟨y, hy, hn⟩ := exists_pt_down hp τ' hτ' y₀ hd.1
      exact k₁ y d (ThG.move hp τ' hτ' hw hL₀ hL₁ hR hy hn hs' hd)
    · obtain ⟨x₀, hx, hn⟩ := exists_pt_up hp τ' hτ' x k₂.1
      have q := ThG.up hp τ' hτ' hw hL₀ hL₁ hR hx hn hs' k₂
      rw [hi] at q
      exact ⟨x₀, c, q, k₃⟩

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem labels_exist : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → Nonempty u.Lab := by
  intro h₁ h₂ h₃ o Ω _ _ _ _ S ρ p _ y₀ u hy
  obtain ⟨q, hq, hq'⟩ := GlobalTheory.ZH.PsiForm.main o Ω S ρ p y₀ u
  obtain ⟨yy, hs, he⟩ := GlobalTheory.T.exists_labelMap_torsion_characters h₁ h₂ h₃ o Ω S ρ p y₀ u
  have hk := GlobalTheory.T.label_map_kernel_eq_integral_torsion h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he hy
  obtain ⟨hi, wt, hw⟩ := GlobalTheory.T.isoFree_perp_labelKernel_weights h₁ h₂ h₃ o Ω S ρ p y₀ u yy hs he
  exact ⟨⟨q, hq, hq', yy, hs, he, hk, hi, wt, hw⟩⟩

end GlobalTheory.ZH
end

