module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.JacobiSymEqOneOfDvdLevel
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.Cover

theorem zeta_mul_mem (F : IntermediateField ℚ ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n.Coprime m)
    (h1 : zeta m ∈ F) (h2 : zeta n ∈ F) : zeta (m * n) ∈ F := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : zeta (m * n) = zeta m ^ u * zeta n ^ v := by
    unfold zeta
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * huv'
  rw [e]
  exact mul_mem (zpow_mem h1 u) (zpow_mem h2 v)

theorem FO_le_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem half_of_split (D : D7) {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K))
    (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (I : Ideal (𝓞 D.host.E))
    (hI : I = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {w0E D}} ∧
      I * I.map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} ∧ I ⊔ I.map (bH D) = ⊤ := by
  obtain ⟨e, he1, he2, hpb⟩ := LPb.pb_eq_JK D hp P hP
  rw [hpb, LPb.map_JK] at hI
  subst hI
  refine ⟨fromK_of_gen ⟨_, rfl, ?_⟩, ?_, ?_⟩
  · rintro y (rfl | hy)
    · exact Subalgebra.natCast_mem _ _
    · rw [Set.mem_singleton_iff.1 hy]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [LPb.QE_map_bar, LPb.QE_mul D _ _ he1 he2]
  · rw [LPb.QE_map_bar, ← Ideal.isCoprime_iff_sup_eq]
    exact LPb.QE_cop_self D _ _ he2

end GlobalTheory.FinalJoin.Cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
section
set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2

theorem liftIndexParameterConditions_of_coreAndShortLaws : ∀ (D : D7) (J : CoreJ D) (T : Top D) (EX : ErrX D) (p : ℕ), LawsJ J → LawsP T → LawsSh T → T.toCore = J.toCore → T.Q.Canon → FieldOK0 D p → HalfEX T.toCore EX → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1 ∧ (T.dδ j n).pd = p) → ∀ j, InR D j → ParOK T EX p j := by
  intro D J T EX p hJ hP hS hT hC hF hH hd j hj
  have key : ∀ C : Core D, C = J.toCore → ∀ j, InR D j → ∀ k k', ((C.U j C.σ₀).X k).Gm = ((C.U j C.σ₀).X k').Gm ∧
      ((C.U j C.σ₀).X k).ξ0 = ((C.U j C.σ₀).X k').ξ0 := by
    rintro C rfl j hj k k'
    obtain ⟨hr, hm⟩ := hJ.modelW j hj J.toCore.σ₀ J.toCore.good_σ₀
    exact ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩
  have hpin : T.Q.Pins := hP.toLawsCore.pins
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hpin.2.1.1
  have hA : T.Q.l.A = 1 := hpin.2.1.2
  have hp : 0 < p := by
    rcases hF.own with e | e
    · exact e ▸ D.host.pde_prime.pos
    · exact e ▸ D.host.pde'_prime.pos
  refine ⟨hS, fun i hi n => (hd i hi n).1, key _ hT, (GlobalTheory.TrivLevel.badN_pos_iff D).2 hF.bad, fun n => (hd j hj n).2,
    (GlobalTheory.PtTie.halfEX_iff_oriented D T hP EX).1 hH, ?_⟩
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D T.Q hpin hC (D.host.g 0 * D.host.g 1 * p)
    (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp) hF.curve j hj T.Q.l (T.Q.Xo j) T.Q.c hA ?_ rfl
  rw [hM]
  exact dvd_mul_right _ _

end GlobalTheory.FinalJoin2
end

