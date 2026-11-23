module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetNeZeroOfOrth
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.UnitarySplit

section Gen

open Formalism.UG

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem val_bc (p : R →+* A) (g : GL n R) : ((bc p g : GL n A) : Matrix n n A) = (g : Matrix n n R).map p := rfl

theorem mat_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {M N : Matrix n n R}
    (h1 : M.map p = N.map p) (h2 : M.map q = N.map q) : M = N := by
  ext i j
  exact hi _ _ (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem gl_ext (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y) {g h : GL n R}
    (h1 : bc p g = bc p h) (h2 : bc q g = bc q h) : g = h :=
  Units.ext (mat_ext p q hi (congrArg Units.val h1) (congrArg Units.val h2))

theorem gl_glue (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (hs : ∀ a b, ∃ x, p x = a ∧ q x = b) (a : GL n A) (b : GL n B) : ∃ g : GL n R, bc p g = a ∧ bc q g = b := by
  choose f hp hq using hs
  let G : Matrix n n A → Matrix n n B → Matrix n n R := fun M N => Matrix.of fun i j => f (M i j) (N i j)
  have Gp : ∀ M N, (G M N).map p = M := fun M N => by ext i j; simp [G, hp]
  have Gq : ∀ M N, (G M N).map q = N := fun M N => by ext i j; simp [G, hq]
  refine ⟨⟨G a.1 b.1, G (a⁻¹).1 (b⁻¹).1, ?_, ?_⟩, Units.ext (Gp _ _), Units.ext (Gq _ _)⟩ <;>
    apply mat_ext p q hi <;> simp [Matrix.map_mul, Gp, Gq]

theorem map_cond (p : R →+* A) (s : R →+* R) (t : A →+* A) (hc : ∀ x, p (s x) = t (p x)) (J g : Matrix n n R) :
    (cT s g * J * g).map p = cT t (g.map p) * J.map p * g.map p := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp [cT, hc]

theorem mem_iff (p : R →+* A) (q : R →+* B) (hi : ∀ x y, p x = p y → q x = q y → x = y)
    (s : R →+* R) (t : A →+* A) (u : B →+* B) (hp : ∀ x, p (s x) = t (p x)) (hq : ∀ x, q (s x) = u (q x))
    (J : Matrix n n R) (g : GL n R) :
    g ∈ UJ s J ↔ bc p g ∈ UJ t (J.map p) ∧ bc q g ∈ UJ u (J.map q) := by
  change cT s g.1 * J * g.1 = J ↔ cT t (g.1.map p) * J.map p * g.1.map p = J.map p ∧
    cT u (g.1.map q) * J.map q * g.1.map q = J.map q
  rw [← map_cond p s t hp, ← map_cond q s u hq]
  exact ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun h => mat_ext p q hi h.1 h.2⟩

theorem mem_of_form (t : A →+* A) (J : Matrix n n A) (g : GL n A)
    (h : ∀ x y, hform t J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform t J x y) : g ∈ UJ t J := by
  change cT t g.1 * J * g.1 = J
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simp only [hform, Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] at this
  rw [Finset.sum_comm] at this
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [this, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

end Gen

section Tens

variable {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem map_sig (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_JR (f : R →ₐ[F] R') {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (JR R J).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = JR R' J := by
  ext i j
  simp [JR, inclR]

end Tens

variable {D : D7}

theorem parts_inj (D : D7) (x y : AE D) (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))

theorem parts_surj (D : D7) (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : AE D, infPart D x = a ∧ finPart D x = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem mem_parts (V : HSp D) (g : GL (Fin V.rank) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram ↔
      Formalism.UG.bc (infPart D) g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram ∧
        Formalism.UG.bc (finPart D) g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have := mem_iff (infPart D) (finPart D) (parts_inj D) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig)
    (sigR _ D.sp.cm.sig) (map_sig _ _) (map_sig _ _) (JR _ V.gram) g
  rw [show (JR _ V.gram).map (infPart D) = JR _ V.gram from map_JR _ _,
    show (JR _ V.gram).map (finPart D) = JR _ V.gram from map_JR _ _] at this
  exact this

theorem ga_ext (V : HSp D) {g h : GA D V} (h1 : infHom V g = infHom V h) (h2 : finHom V g = finHom V h) : g = h :=
  Subtype.ext (gl_ext (infPart D) (finPart D) (parts_inj D) h1 h2)

theorem ga_glue (V : HSp D) (a : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (b : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) (ha : a ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram)
    (hb : b ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) : ∃ g : GA D V, infHom V g = a ∧ finHom V g = b := by
  obtain ⟨g, h1, h2⟩ := gl_glue (infPart D) (finPart D) (parts_inj D) (parts_surj D) a b
  exact ⟨⟨g, (mem_parts V g).2 ⟨h1 ▸ ha, h2 ▸ hb⟩⟩, h1, h2⟩

theorem infHom_mem (V : HSp D) (g : GA D V) : infHom V g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).1

theorem finHom_mem (V : HSp D) (g : GA D V) : finHom V g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
  ((mem_parts V (matHom V g)).1 (Subtype.property (p := fun x => x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) g)).2

theorem hermA_eq (V : HSp D) (x y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y =
      Formalism.UG.hform (sigR (Af D.host.F) D.sp.cm.sig) (JR (Af D.host.F) V.gram) y x := by
  unfold GlobalTheory.AdLat.hermA Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change x b * (JR (Af D.host.F) V.gram a b) * sigR (Af D.host.F) D.sp.cm.sig (y a) = _
  ring

theorem real_finite_split : ∀ (D : D7) (V : HSp D), (∀ h : GA D V, ∃ a ∈ GinfC V, ∃ k ∈ GfC V, h = a * k) ∧ (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧ (∀ h : GA D V, h ∈ GinfC V → h ∈ GfC V → h = 1) ∧ (∀ g : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), (∀ x y, GlobalTheory.AdLat.hermA (cF D) V.gramᵀ (g.1 *ᵥ x) (g.1 *ᵥ y) = GlobalTheory.AdLat.hermA (cF D) V.gramᵀ x y) → ∃ k ∈ GfC V, finHom V k = g) ∧ ∀ g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E), g ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram → ∃ a ∈ GinfC V, infHom V a = g := by
  intro D V
  refine ⟨fun h => ?_, fun a ha k hk => ?_, fun h h1 h2 => ?_, fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V _ 1 (infHom_mem V h) (one_mem _)
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 _ (one_mem _) (finHom_mem V h)
    refine ⟨a, a2, k, k1, ga_ext V ?_ ?_⟩
    · rw [map_mul, a1, k1, mul_one]
    · rw [map_mul, a2, k2, one_mul]
  · have a2 : finHom V a = 1 := ha
    have k1 : infHom V k = 1 := hk
    refine ga_ext V ?_ ?_
    · rw [map_mul, map_mul, k1, mul_one, one_mul]
    · rw [map_mul, map_mul, a2, mul_one, one_mul]
  · have a2 : finHom V h = 1 := h1
    have k1 : infHom V h = 1 := h2
    exact ga_ext V (by rw [k1, map_one]) (by rw [a2, map_one])
  · have hm : g ∈ HR (Af D.host.F) D.sp.cm.sig V.gram :=
      mem_of_form _ _ g fun x y => by rw [← hermA_eq, ← hermA_eq, hg]
    obtain ⟨k, k1, k2⟩ := ga_glue V 1 g (one_mem _) hm
    exact ⟨k, k1, k2⟩
  · obtain ⟨a, a1, a2⟩ := ga_glue V g 1 hg (one_mem _)
    exact ⟨a, a2, a1⟩

end GlobalTheory.UnitarySplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem hT_symm_equivFun {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) =
      ∑ a, ∑ b, y a * V.gramᵀ a b * star (x b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.transpose_apply, HSpace.gram]
  ring

theorem mem_latC {D : D7} (V : HSp D) (v : Fin V.rank → D.host.E) :
    v ∈ latC V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, V.frame.equivFun.apply_symm_apply v⟩

theorem gram_transpose_det_ne_zero {D : D7} (V : HSp D) : V.gramᵀ.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  have h1 : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    obtain ⟨x, rfl⟩ := V.frame.equivFun.symm.surjective x
    rw [hT_symm_equivFun, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ a, v a * V.gramᵀ a b = 0 := congrFun h0 b
    rw [this, zero_mul]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h1

theorem latHat_eq_hat_and_gram :
    ∀ (D : D7) (V : HSp D), latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) ∧ (∀ v, finVec V v = GlobalTheory.AdLat.fv D.host.F v) ∧ (latC V).FG ∧ Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (∀ x, cF D (cF D x) = x) ∧ (∀ x, cF D x = cc x) ∧ cF D ≠ 1 ∧ (∀ a b, cF D (V.gramᵀ a b) = V.gramᵀ b a) ∧ V.gramᵀ.det ≠ 0 ∧ (∀ x y, V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm y) = -herm (-V.gramᵀ) y x) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V := by
  intro D V
  refine ⟨?_, fun v => rfl, ?_, ?_, fun x => star_star x, fun x => rfl, ?_, ?_,
    gram_transpose_det_ne_zero V, ?_, ?_⟩
  · unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  · exact V.standardTuple_isLattice.fg.map _
  · rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hspan]; trivial
    have := Submodule.mem_map_of_mem (f := V.frame.equivFun.toLinearMap) hx
    rw [Submodule.map_span] at this
    exact this
  · intro h
    apply IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    have hx : cF D x = x := by rw [h]; rfl
    exact hx
  · intro a b
    exact V.herm.eq _ _
  · intro x y
    rw [hT_symm_equivFun]
    simp only [herm, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  · intro v
    rw [mem_latC]
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    have key : V.frame.equivFun.symm v ∈ Formalism.HermitianLatticesTheory.dual V.hT V.L0 ↔
        ∀ y ∈ V.L0, V.hT y (V.frame.equivFun.symm v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
      rfl
    rw [key]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective y
      rw [hT_symm_equivFun, Submodule.mem_one]
      exact (FractionalIdeal.mem_one_iff _).1 (h y ((mem_latC V y).2 hy))
    · intro h y hy
      have := h _ ((mem_latC V y).1 hy)
      rw [hT_symm_equivFun, Submodule.mem_one] at this
      exact (FractionalIdeal.mem_one_iff _).2 this

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonCompare

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def archHom (V : HSp D) (τ : D.host.E →+* ℂ) : GA D V →* Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  if h : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ then
    h.choose.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (infHom V))
  else 1

theorem archHom_eq (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) (g : GA D V) : archHom V τ g = Pj.archM V θ g := by
  have h' : ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ := ⟨θ, h⟩
  rw [archHom, dite_eq_left h', GlobalTheory.LettersCheck.isInfEmb_unique τ _ θ h'.choose_spec h]
  rfl

theorem isHermitian_gram (V : HSp D) (τ : D.host.E →+* ℂ) : (V.gram.map τ).IsHermitian := by
  ext a b
  have h := V.herm.eq (V.frame b) (V.frame a)
  show star (τ (V.hT (V.frame b) (V.frame a))) = τ (V.hT (V.frame a) (V.frame b))
  rw [← h]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem lintegral_adelic (V : HSp D) {Comp : Type} [Fintype Comp] {r : ℕ} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hU : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (hΨ : ∀ k k', (X k).Ψ = (X k').Ψ ∧ (X k).p0 = (X k').p0) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (h0 : μ 𝓕 ≠ 0) (h1 : μ 𝓕 ≠ ⊤) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : ∀ k, Frame (X k).Ψ r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor (X k).Ψ r, ∀ x ∈ (X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun g => F (dict g).1 (dict g).2) ∧
        ∫⁻ g in 𝓕, F (dict g).1 (dict g).2 ∂μ = κ * ∑ k, IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt (X k) (F k) := by
  subst hr
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  haveI : μ.IsMulRightInvariant := ⟨GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) μ h𝓕 h0 h1⟩
  have hmem : ∀ h, h ∈ (Kf.map (finHom V)).comap (finHom V) ↔ ∃ a ∈ GinfC V, ∃ z ∈ Kf, h = a * z := by
    intro h
    constructor
    · rintro ⟨z, hz, e⟩
      refine ⟨h * z⁻¹, ?_, z, hz, (inv_mul_cancel_right _ _).symm⟩
      show finHom V (h * z⁻¹) = 1
      rw [map_mul, map_inv, e, mul_inv_cancel]
    · rintro ⟨a, ha, z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [map_mul, show finHom V a = 1 from ha, one_mul]
  have hopen : IsOpen (((Kf.map (finHom V)).comap (finHom V) : Subgroup (GA D V)) : Set (GA D V)) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK 1) ?_)
    rintro _ ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [one_mul, map_mul, show finHom V a = 1 from ha, mul_one]
  have hg := fun k => (GlobalTheory.UnitaryGlue.adelic_glue D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have ha : ∀ k (τ : (X k).Ψ) g, archHom V τ.1 g = Pj.archM V (th k τ) g := fun k τ g => archHom_eq V (hth k τ) g
  have htr : ∀ (u J : Matrix (Fin V.rank) (Fin V.rank) ℂ), uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ ↔
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u J
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  obtain ⟨dL, dR, ⟨x0, d0, dI⟩, dD, -, dF⟩ := hd
  refine lintegral_dict X μ (GQ V) (GinfC V) Kf _ h𝓕 h0 h1 hopen.measurableSet hmem dict (archHom V)
    (fun τ => (V.gram.map τ)ᵀ) x0 hΨ (fun τ => ⟨(isHermitian_gram V τ).transpose, ?_⟩) (fun k τ => ?_)
    (fun k τ g => ?_) (fun k u hu => ?_) (fun k τ z hz => ?_) (fun k γ hγ h => ?_) dL dR d0 (fun g h hh => ?_) dD dF hU
  · rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)
  · exact ((hg k).2.2.1 τ).congr fun g => (ha k τ g).symm
  · rw [htr, ha]
    exact GlobalTheory.RecDictModel.archM_unitary V (hth k τ) g
  · obtain ⟨h, hh, e⟩ := (hg k).2.2.2 u fun τ => (htr _ _).1 (hu τ)
    exact ⟨h, hh, fun τ => (ha k τ h).trans (e τ)⟩
  · rw [ha, Pj.archM, show infHom V z = 1 from ((hK z).1 hz).1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      by_cases hτ : τ ∈ (X k).Ψ
      · exact ⟨⟨τ, hτ⟩⟩
      · exact ⟨⟨_, not_not.1 (mt ((X k).cmType τ).2 hτ)⟩⟩
    obtain ⟨γ₀, -, e0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have e1 : (matHom V γ).1 = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (AF D.host.F)) := (congrArg Units.val e0).symm
    have e2 : Pj.archM V (th k τ) γ = (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
      have : ((γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Ainf D.host.F))).map (th k τ) =
          (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 := by
        ext i j
        exact (hth k τ).1 _
      rw [← this, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← e1]
      rfl
    have e3 : (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 := by
      refine Matrix.map_injective τ.1.injective ?_
      show (γ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1
      rw [← e2, ← ha, h τ, Matrix.map_one _ (map_zero _) (map_one _)]
    refine Subtype.ext (Units.ext (e1.trans ?_))
    rw [e3]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · simp only [ha]
    exact dI g h hh

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Pj.Unf Xo c σ r)

theorem measurable_onQ_adel (V : HSp D) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D V → Σ k, Frame (X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r} {N : ℕ} (hN : 0 < N)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hd : Pj.DictIsUnif V dict Kf th hr) (hK : Pj.IsLevelK V N Kf)
    (hm : Pj.MuUnit V dict mu) (hc : Continuous mu) (P : Pj.FDSec X) (hP : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) :
    Measurable (Pj.onQ V (Pj.adel V dict mu P)) := by
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((hK k).1 hk).1)
    (GlobalTheory.LevelOpen.level_mem_nhds D V N Kf hN hK) fun k τ => ⟨τ.1, hth k τ⟩
  have hC : Continuous fun g => mu g * P (dict g).1 (dict g).2 := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨M, hM, k, x, hx, hs⟩ := hloc g₀
    have h1 : ContinuousOn (fun g => mu g * P k (x g)) M :=
      hc.continuousOn.mul ((hP k).comp hx fun g hg => (hs g hg).1)
    refine (h1.continuousAt hM).congr ?_
    filter_upwards [hM] with g hg
    obtain ⟨hxd, γ, hγ, he⟩ := hs g hg
    rw [he]
    exact congrArg (mu g * ·) (hΓ k γ hγ _ hxd).symm
  have hL : ∀ g g', g * g'⁻¹ ∈ GQ V → mu g' * P (dict g').1 (dict g').2 = mu g * P (dict g).1 (dict g).2 := by
    intro g g' h4
    obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 g'
    have e' := hm.1 (g * g'⁻¹) g'
    rw [inv_mul_cancel_right] at e e'
    rw [hm.2.2.1 _ h4, one_mul] at e'
    rw [e, e']
    exact congrArg (mu g' * ·) (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  rw [measurable_from_quotient]
  have : (Pj.onQ V (Pj.adel V dict mu P) ∘ Quotient.mk'') = fun g => mu g * P (dict g).1 (dict g).2 :=
    funext fun g => hL g (Pj.autMk V g).out (QuotientGroup.rightRel_apply.1 (Quotient.mk_out g))
  rw [this]
  exact hC.measurable

end GlobalTheory.PeterssonCompare
end
end

