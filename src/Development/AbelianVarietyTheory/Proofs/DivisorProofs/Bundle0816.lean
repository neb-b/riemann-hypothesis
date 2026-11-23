module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MulMemIntA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoords
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieCoordMult

theorem lieMult_iff_finrank_eig : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  intro W _ G _ _ O _ act n k _ β T A hinj htan hadd hsc hact τ N
  set E : Submodule k (Fin n → k) :=
    ⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) with hE
  have memE : ∀ x, x ∈ E ↔ ∀ a, (A a).mulVec x = τ a • x := by
    intro x
    simp [hE, Submodule.mem_iInf, sub_eq_zero]
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → k)), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ w, IsLieEigen act (spMap β) τ w ↔ ∃ x ∈ E, w = T x := by
    intro w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := (htan w).1 h1
      refine ⟨x, (memE x).2 fun a => hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2 a, hsc]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(htan _).2 ⟨x, rfl⟩, fun a => ?_⟩
      rw [hact, (memE x).1 hx a, hsc]
      rfl
  have comb : ∀ (x : Fin N → (Fin n → k)) (y : Fin n → k) (c : Fin N → k),
      (∃ u : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (T (x i)).left) ∧
        T y = (List.ofFn u).prod) ↔ y = ∑ i, c i • x i := by
    intro x y c
    constructor
    · rintro ⟨u, hu, hy⟩
      have hu' : u = fun i => T (c i • x i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (hsc _ _).symm)
      rw [hu', Tsum] at hy
      exact hinj hy
    · intro hy
      exact ⟨fun i => T (c i • x i), fun i => hsc _ _, by rw [Tsum, hy]⟩
  show (∃ v : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, IsLieEigen act (spMap β) τ (v i)) ∧ ∀ w, IsLieEigen act (spMap β) τ w →
    ∃! c : Fin N → k, ∃ u : Fin N → (epsPt (spMap β) ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔ _
  constructor
  · rintro ⟨v, hv, H⟩
    choose x hxE hx using fun i => (eig _).1 (hv i)
    obtain rfl : v = fun i => T (x i) := funext hx
    let b : Fin N → E := fun i => ⟨x i, hxE i⟩
    have bij : Function.Bijective (Fintype.linearCombination k b) := by
      refine (Function.bijective_iff_existsUnique _).2 fun y => ?_
      refine (existsUnique_congr fun c => ?_).1 (H (T y) ((eig _).2 ⟨y, y.2, rfl⟩))
      rw [comb x y c, Subtype.ext_iff, Fintype.linearCombination_apply]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, b]
      exact eq_comm
    rw [← (LinearEquiv.ofBijective _ bij).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq k E h
    refine ⟨fun i => T (b i), fun i => (eig _).2 ⟨_, (b i).2, rfl⟩, fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (eig w).1 hw
    refine (existsUnique_congr fun c => ?_).2
      ((Function.bijective_iff_existsUnique _).1 b.equivFun.symm.bijective ⟨y, hy⟩)
    rw [comb (fun i => (b i : Fin n → k)) y c, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact eq_comm

end GlobalTheory.LieCoordMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingObstructionEqOfCohomologousCocycles
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObU_of_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' t c hfun hrel hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hlift : ∀ T, ∃ τ : (L.B T)ˣ, L.p T (τ : L.B T) = (t T : F.obj T) := by
    intro T
    obtain ⟨b, hb⟩ := L.surj T (t T : F.obj T)
    obtain ⟨b', hb'⟩ := L.surj T (((t T)⁻¹ : (F.obj T)ˣ) : F.obj T)
    have hn : L.p T (b * b' - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hb, hb']; simp
    rw [L.ker] at hn
    have hnil : IsNilpotent (b * b' - 1) := by
      refine ⟨2, ?_⟩
      have h2 : (b * b' - 1) ^ 2 ∈ (I.map (algebraMap R (L.B T))) ^ 2 := Ideal.pow_mem_pow hn 2
      rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h2
      simpa using h2
    have hu : IsUnit (b * b') := by simpa using hnil.isUnit_one_add
    exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simp [hb]⟩
  choose τ hτ using hlift
  let ρu : ∀ {T T' : C} (_ : T ⟶ T'), (L.B T)ˣ →* (L.B T')ˣ := fun a ↦ Units.map (L.ρ a).toRingHom.toMonoidHom
  refine ⟨fun T T' a ↦ τ T' * v T T' a * (ρu a (τ T))⁻¹, σ, z, ?_, hσ, hc, ?_⟩
  · intro T T' a
    have hm : IsUnit (mp F a (t T : F.obj T)) := (t T).isUnit.map (mp F a)
    have hinv : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
      have := (ρu a (τ T)).inv_mul
      simpa [ρu] using this
    refine (hm.mul_left_inj).mp ?_
    have key : L.p T' (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.p T' (L.ρ a (τ T : L.B T)) = 1 := by
      rw [← map_mul, hinv, map_one]
    rw [hrel, ← hτ T, ← L.nat a]
    simp only [Units.val_mul, map_mul]
    rw [_root_.mul_assoc _ (L.p T' _), key, _root_.mul_one, hτ T', hv]
  · intro T T' T'' a b
    refine ⟨(hz T T' T'' a b).1, ?_⟩
    have hzb := (hz T T' T'' a b).2
    have e1 : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have h : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
        simpa [ρu] using (ρu a (τ T)).inv_mul
      rw [← map_mul, h, map_one]
    have e2 : (((ρu b (τ T'))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (τ T' : L.B T') = 1 := by
      have := (ρu b (τ T')).inv_mul
      simpa [ρu] using this
    have e3 : (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have := (ρu (a ≫ b) (τ T)).inv_mul
      rw [← hfun a b]
      simpa [ρu] using this
    have he : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) = (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') := by
      linear_combination (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * e1 - (L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T'))) * e3
    simp only [Units.val_mul, map_mul]
    rw [he]
    linear_combination ((τ T'' : L.B T'') * L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * e2 + ((τ T'' : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * hzb

end GlobalTheory.LBObs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdeles
section
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrdLift

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem mul_mem_intA {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hx : x ∈ GlobalTheory.PlaceComp.intA F E)
    (hy : y ∈ GlobalTheory.PlaceComp.intA F E) : x * y ∈ GlobalTheory.PlaceComp.intA F E :=
  by apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption

end GlobalTheory.OrdLift

theorem GlobalTheory.OrdLift.ordAt_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E),
    a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  intro F E _ _ _ _ _ v a ha
  induction ha using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E),
      AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _
    rw [GlobalTheory.SplitIdem.evalV_singleV_same]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | one =>
    refine ⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩
    simp [Algebra.TensorProduct.one_def]
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s + t, add_mem hs ht, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨-s, neg_mem hs, map_neg _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatCharPowEqDetPow
section
noncomputable section

namespace GlobalTheory.DefPt

open Matrix

section Char

variable {K : Type} [Field K] {n : ℕ} (χ : Matrix (Fin n) (Fin n) K →* K)

theorem matChar_submatrix (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) K) :
    χ (M.submatrix σ σ) = χ M := by
  have h1 : ∀ N : Matrix (Fin n) (Fin n) K,
      σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ := by
    intro N
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    rfl
  have h2 := congrArg χ (h1 1)
  rw [submatrix_one_equiv, Matrix.mul_one, map_mul, map_one] at h2
  rw [← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]

theorem matChar_transvection [CharZero K] {i j : Fin n} (hij : i ≠ j) (c : K) :
    χ (transvection i j c) = 1 := by
  set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)
  set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have hD : χ D ≠ 0 := fun h => by
    have := congrArg χ hDD
    rw [map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hT : χ (transvection i j c) ≠ 0 := fun h => by
    have := congrArg χ (transvection_mul_transvection_same i j hij c (-c))
    rw [add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hcomm : D * transvection i j c = transvection i j (c + c) * D := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    have hdi : Function.update (1 : Fin n → K) i 2 i = 2 := by simp
    have hdj : Function.update (1 : Fin n → K) i 2 j = 1 := by simp [Ne.symm hij]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hij, hdi, hdj]
      simp only [and_self, ite_true]
      ring
    · have h' : ¬(i = a ∧ j = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg h', if_neg h']
      simp only [add_zero]
      by_cases hab : a = b
      · subst hab; ring
      · rw [Matrix.one_apply_ne hab]; ring
  have e := congrArg χ hcomm
  rw [map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)] at e
  have e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c) := by
    rw [mul_one]
    exact mul_right_cancel₀ hD e
  exact (mul_left_cancel₀ hT e2).symm

theorem matChar_mulSingle (k k' : Fin n) (a : K) :
    χ (diagonal (Pi.mulSingle k a)) = χ (diagonal (Pi.mulSingle k' a)) := by
  rw [← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]
  apply congrArg χ
  apply congrArg diagonal
  funext x
  simp only [Function.comp_apply]
  by_cases hx : x = k
  · subst hx; simp
  · by_cases hx' : x = k'
    · subst hx'; rw [Equiv.swap_apply_right]; simp [hx, Ne.symm hx]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; simp [hx, hx']

theorem matChar_diagonal_pow (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m) (d : Fin n → K) :
    χ (diagonal d) ^ n = (diagonal d).det ^ m := by
  let ψ : (Fin n → K) →* K := χ.comp (diagonalRingHom (Fin n) K).toMonoidHom
  have hψ : ∀ v, ψ v = χ (diagonal v) := fun v => rfl
  have hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m := by
    intro k a
    calc χ (diagonal (Pi.mulSingle k a)) ^ n = ∏ k' : Fin n, ψ (Pi.mulSingle k' a) := by
          rw [Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]
  calc χ (diagonal d) ^ n = (∏ k, ψ (Pi.mulSingle k (d k))) ^ n := by
        rw [← map_prod, Finset.univ_prod_mulSingle, hψ]
    _ = ∏ k, d k ^ m := by
        rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun k _ => hone k (d k)
    _ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]

theorem matChar_pow_eq_det_pow [CharZero K] (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m)
    (g : Matrix (Fin n) (Fin n) K) : χ g ^ n = g.det ^ m := by
  refine diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g
    (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)
  · show χ t.toMatrix ^ n = t.toMatrix.det ^ m
    rw [show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij,
      det_transvection_of_ne _ _ t.hij]
    simp
  · show χ (A * B) ^ n = (A * B).det ^ m
    have hA' : χ A ^ n = A.det ^ m := hA
    have hB' : χ B ^ n = B.det ^ m := hB
    rw [map_mul, det_mul, mul_pow, mul_pow, hA', hB']

end Char

end GlobalTheory.DefPt

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine MvPolynomial
open scoped Matrix

def rhoDetHom {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : Matrix (Fin n) (Fin n) K →* K where
  toFun g := (GlobalTheory.DefPt.rhoMat la g).det
  map_one' := by rw [Model.rhoMat_one, Matrix.det_one]
  map_mul' g h := by rw [Model.rhoMat_mul, Matrix.det_mul, mul_comm]

theorem det_rhoMat_pow : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la →
    ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) := by
  intro K _ _ n la _ g
  have hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la) := by
    intro t
    show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _
    rw [Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]
  exact matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g

end GlobalTheory.DefPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlaces
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open Filter Topology

namespace GlobalTheory.SUTrunc

section Mat

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {e : R}

theorem idempotentTruncation_preserves_form (he : e * e = e) {A B J : Matrix n n R} (h : A * J * B = J) :
    (1 + e • (A - 1)) * J * (1 + e • (B - 1)) = J := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub, smul_smul, he, h]
  abel

theorem trunc_mul (he : e * e = e) {A B : Matrix n n R} (h : A * B = 1) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 := by
  have := idempotentTruncation_preserves_form he (A := A) (B := B) (J := 1) (by rw [Matrix.mul_one, h])
  rwa [Matrix.mul_one] at this

theorem cT_trunc (c : R →+* R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hc]
  · simp [Formalism.UG.cT, hc, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem det_trunc (he : e * e = e) {A : Matrix n n R} (h : A.det = 1) : (1 + e • (A - 1)).det = 1 := by
  have key : ∀ (a : R) (B : Matrix n n R), B.det = 1 → (∀ i j, a ∣ (1 + e • (A - 1)) i j - B i j) →
      a ∣ (1 + e • (A - 1)).det - 1 := by
    intro a B hB hd
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, ← hB, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hd i j
  obtain ⟨x, hx⟩ := key e 1 Matrix.det_one fun i j => ⟨(A - 1) i j, by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring⟩
  obtain ⟨y, hy⟩ := key (1 - e) A h fun i j => ⟨-((A - 1) i j), by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]; ring⟩
  linear_combination (1 - e) * hx + e * hy + (-x - y) * he

end Mat

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (h : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, mul_one]
    · rw [h2 w hw, mul_zero]
  · change evalV F v (sndA F η) * evalV F v (sndA F η) = evalV F v (sndA F η)
    by_cases hw : v ∈ S₂
    · rw [h3 v hw, mul_one]
    · rw [h4 v hw, mul_zero]

theorem tendsto_idem (η : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hη : ∀ T, IsPlacesIdem Finset.univ T (η T)) : Tendsto η atTop (𝓝 1) := by
  classical
  let y : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun T v => if v ∈ T then 1 else 0
  have hy : Tendsto y atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {v}] with T hT
    exact (if_pos (hT (Finset.mem_singleton_self v))).symm
  let s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : Continuous fun z => pairA F 1 (s z) := continuous_const.prodMk hs
  have h1 : pairA F 1 (s 1) = 1 := rfl
  have h2 : η = fun T => pairA F 1 (s (y T)) := by
    funext T
    obtain ⟨h1, -, h3, h4⟩ := hη T
    refine Prod.ext (funext fun w => h1 w (Finset.mem_univ w)) (RestrictedProduct.ext _ _ fun v => ?_)
    change evalV F v (sndA F (η T)) = ((y T v : v.adicCompletionIntegers F) : v.adicCompletion F)
    by_cases hv : v ∈ T
    · rw [h3 v hv]; simp [y, hv]
    · rw [h4 v hv]; simp [y, hv]
  rw [h2, ← h1]
  exact (hp.tendsto 1).comp hy

theorem mem_closure_supp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  intro F E _ _ _ _ _ σ _ M J _ g hg
  choose η hη using fun T : Finset (HeightOneSpectrum (𝓞 F)) => StrongApprox.exists_isPlacesIdem Finset.univ T
  have hlim := tendsto_idem η hη
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have he : ∀ T, ι (η T) * ι (η T) = ι (η T) := fun T => by rw [← map_mul, idem_mul_self (hη T)]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin M) (AF F ⊗[F] E) := fun T =>
    ⟨1 + ι (η T) • (SUSuppSub.mv σ J g - 1), 1 + ι (η T) • (SUSuppSub.mv σ J g⁻¹ - 1),
      trunc_mul (he T) (SUSuppSub.mv_mul_inv σ J g), trunc_mul (he T) (SUSuppSub.mv_inv_mul σ J g)⟩
  have hu : ∀ T, u T ∈ HR (AF F) σ J := by
    intro T
    change Formalism.UG.cT (sigR (AF F) σ) (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) * JR (AF F) J *
      (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) = JR (AF F) J
    rw [cT_trunc _ (StrongApprox.sigR_algebraMap σ _)]
    exact idempotentTruncation_preserves_form (he T) (g : HR (AF F) σ J).2
  let x : Finset (HeightOneSpectrum (𝓞 F)) → HA (AF F) σ J := fun T => (⟨u T, hu T⟩ : HR (AF F) σ J)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hmat : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Tendsto (fun T => 1 + ι (η T) • (A - 1)) atTop (𝓝 A) := by
    intro A
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (hlim.smul_const ((A - 1) i j)).const_add ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    rw [one_smul, Matrix.sub_apply, add_sub_cancel] at h
    refine h.congr fun T => ?_
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Algebra.smul_def]
  have hx : Tendsto x atTop (𝓝 g) := by
    refine (tendsto_subtype_rng (p := fun a => a ∈ HR (AF F) σ J)).2 ?_
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    exact (hmat (SUSuppSub.mv σ J g)).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (hmat (SUSuppSub.mv σ J g⁻¹)))
  refine mem_closure_of_tendsto hx (Eventually.of_forall fun T => ⟨Finset.univ, T, η T, hη T, ?_⟩)
  rw [SUSuppSub.mem_SUSupp_iff]
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_trunc (he T) (StrongApprox.mem_SUAdelic.1 hg)), ?_⟩
  change ι (η T) • (1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1) = 1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1
  rw [add_sub_cancel_left, smul_smul, he]

end GlobalTheory.SUTrunc

end
end

