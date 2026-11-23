module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrime
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LatIdem

theorem exists_iterate_idem {X : Type*} [Finite X] (u : X → X) : ∃ N : ℕ, 0 < N ∧ u^[2 * N] = u^[N] := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ u^[i] = u^[j] := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => u^[n])
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact ⟨i, j, h1, h⟩
    · exact ⟨j, i, h1, h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have key : ∀ m : ℕ, u^[i + m * (k + 1)] = u^[i] := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : i + (m + 1) * (k + 1) = (i + m * (k + 1)) + (k + 1) := by ring
      rw [this, Function.iterate_add, ih, ← Function.iterate_add, ← add_assoc, ← h]
  refine ⟨(i + 1) * (k + 1), by positivity, ?_⟩
  have e1 : 2 * ((i + 1) * (k + 1)) = (i + (i + 1) * (k + 1)) + (i * k + k + 1) := by ring
  have e2 : (i + 1) * (k + 1) = i + (i * k + k + 1) := by ring
  rw [e1, Function.iterate_add, key, ← Function.iterate_add, ← e2]

theorem exists_idem_mod {M : Type*} [AddCommGroup M] (Λ P : AddSubgroup M) (g : M →+ M)
    (hΛ : ∀ z ∈ Λ, g z ∈ Λ) (hP : ∀ z ∈ P, g z ∈ P) [Finite (Λ.map (QuotientAddGroup.mk' P))] :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ Λ, g^[2 * N] z - g^[N] z ∈ P := by
  let gb : M ⧸ P →+ M ⧸ P := QuotientAddGroup.map P P g hP
  let u : Λ.map (QuotientAddGroup.mk' P) → Λ.map (QuotientAddGroup.mk' P) := fun x => ⟨gb x, by
    obtain ⟨_, z, hz, rfl⟩ := x
    exact ⟨g z, hΛ z hz, rfl⟩⟩
  have hu : ∀ (n : ℕ) (z : M) (hz : z ∈ Λ), (u^[n] ⟨QuotientAddGroup.mk' P z, z, hz, rfl⟩ : M ⧸ P) =
      QuotientAddGroup.mk' P (g^[n] z) := by
    intro n
    induction n with
    | zero => intro z hz; rfl
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show gb _ = _
      rw [ih z hz]; rfl
  obtain ⟨N, hN, h⟩ := exists_iterate_idem u
  refine ⟨N, hN, fun z hz => ?_⟩
  have := hu (2 * N) z hz
  rw [h, hu N z hz] at this
  exact QuotientAddGroup.eq_iff_sub_mem.1 this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.EmbChart GlobalTheory.InertSph

theorem at_atPlace (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (atPlace v a) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem eq_atPlace (v : Pl (F := F)) (a : AF F) (ha : At (evFin F v) a) : a = atPlace v (evFin F v a) := by
  have h := ha (1 - atPlace v 1) (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, atPlace_mul_right, one_mul, sub_eq_zero] at h
  exact h

omit [NumberField E] in
theorem gen_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (c : v.adicCompletionIntegers F) (y : Fin d → E) (hy : y ∈ W.L) :
    (atPlace v (c : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
  AddSubgroup.subset_closure ⟨_, at_atPlace v _, by rw [evFin_atPlace]; exact c.2, y, hy, rfl⟩

theorem finite_mod {d : ℕ} (W : Spc F E d) (hW : W.L.FG) (v : Pl (F := F)) (p : ℕ) (hp : 0 < p) :
    Finite ((latAt W v).map (QuotientAddGroup.mk' ((latAt W v).map (nsmulAddMonoidHom p)))) := by
  set P := (latAt W v).map (nsmulAddMonoidHom p) with hPdef
  have hp0 : (p : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    have h1 : ((p : v.adicCompletionIntegers F) : Fv F v) = 0 := congrArg Subtype.val h
    have h2 : (p : Fv F v) = 0 := by simpa using h1
    rw [← map_natCast (algebraMap F (Fv F v)), map_eq_zero] at h2
    exact (Nat.cast_ne_zero.2 hp.ne') h2
  have hfin : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  obtain ⟨T, hT⟩ : (W.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.2 hW
    have : Module.Finite ℤ W.L := Module.Finite.trans (𝓞 E) W.L
    exact Module.Finite.iff_fg.1 this
  have hTL : ∀ t ∈ T, t ∈ W.L := fun t ht => by
    have : t ∈ W.L.restrictScalars ℤ := hT ▸ Submodule.subset_span ht
    exact this
  let s : (v.adicCompletionIntegers F ⧸ Ideal.span {(p : v.adicCompletionIntegers F)}) × T → (Fin d → AE F E) ⧸ P :=
    fun x => QuotientAddGroup.mk' P
      (atPlace v ((x.1.out : v.adicCompletionIntegers F) : Fv F v) • fun i => inclR (F := F) (AF F) (x.2.1 i))
  have heq : (latAt W v).map (QuotientAddGroup.mk' P) = AddSubgroup.closure (Set.range s) := by
    apply le_antisymm
    · rw [AddSubgroup.map_le_iff_le_comap, InertSph.latAt, AddSubgroup.closure_le]
      rintro _ ⟨a, ha, hav, y, hy, rfl⟩
      have hy' : y ∈ Submodule.span ℤ (T : Set (Fin d → E)) := hT ▸ hy
      clear hy
      rw [SetLike.mem_coe]
      induction hy' using Submodule.span_induction with
      | mem t ht =>
        let x : v.adicCompletionIntegers F := ⟨_, hav⟩
        let q := Ideal.Quotient.mk (Ideal.span {(p : v.adicCompletionIntegers F)}) x
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out q).symm)
        have hc' : evFin F v a - ((q.out : v.adicCompletionIntegers F) : Fv F v) = p • (c : Fv F v) := by
          have := congrArg Subtype.val hc
          simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, AddSubgroupClass.coe_sub] at this
          rw [nsmul_eq_mul, mul_comm]; exact this.symm
        rw [AddSubgroup.mem_comap]
        refine AddSubgroup.subset_closure ⟨(q, ⟨t, ht⟩), ?_⟩
        refine (QuotientAddGroup.eq_iff_sub_mem.2 ?_).symm
        refine ⟨_, gen_mem W v c t (hTL t ht), ?_⟩
        rw [← sub_smul, eq_atPlace v a ha, ← map_sub, hc', map_nsmul, smul_assoc]
        rfl
      | zero =>
        have : (a • fun i => inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := by
          funext i; simp
        rw [this]; exact zero_mem _
      | add x y _ _ hx hy =>
        have : (a • fun i => inclR (F := F) (AF F) ((x + y) i)) =
            (a • fun i => inclR (F := F) (AF F) (x i)) + (a • fun i => inclR (F := F) (AF F) (y i)) := by
          funext i; simp
        rw [this]; exact add_mem hx hy
      | smul n x _ hx =>
        have : (a • fun i => inclR (F := F) (AF F) ((n • x) i)) =
            n • (a • fun i => inclR (F := F) (AF F) (x i)) := by
          funext i
          simp only [Pi.smul_apply, map_zsmul]
          rw [smul_comm]
        rw [this]; exact zsmul_mem hx n
    · rw [AddSubgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, gen_mem W v _ _ (hTL _ x.2.2), rfl⟩
  have hfg : ((latAt W v).map (QuotientAddGroup.mk' P)).FG :=
    (AddSubgroup.fg_iff _).2 ⟨_, heq.symm, Set.finite_range s⟩
  have : AddGroup.FG ((latAt W v).map (QuotientAddGroup.mk' P)) := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine AddCommGroup.finite_of_fg_isAddTorsion _ ?_
  rintro ⟨_, z, hz, rfl⟩
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p, hp, Subtype.ext ?_⟩
  show p • QuotientAddGroup.mk' P z = 0
  rw [← map_nsmul]
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz, rfl⟩

theorem exists_pow_idem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl (F := F)) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  intro F E _ _ _ _ _ d W hW v p hp _ f hf
  have := finite_mod W hW.fg v p hp
  let g : (Fin d → AE F E) →+ (Fin d → AE F E) := (Matrix.mulVecLin f).toAddMonoidHom
  have hg : ∀ (n : ℕ) (z : Fin d → AE F E), g^[n] z = (f ^ n) *ᵥ z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, pow_succ', ← Matrix.mulVec_mulVec]; rfl
  obtain ⟨N, hN, h⟩ := exists_idem_mod (latAt W v) ((latAt W v).map (nsmulAddMonoidHom p)) g hf (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨g z, hf z hz, (map_nsmul g p z).symm⟩)
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨y, hy, e⟩ := h z hz
  rw [hg, hg] at e
  exact ⟨y, hy, e.symm⟩

end GlobalTheory.LatIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonzeroOnClosedFibreCompleteLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

namespace GlobalTheory.ThetaClosed

theorem nonzeroLocus_firstPower_section_subset {X : Scheme.{0}} {L : LB X} (σ : H0 L 1) {x : X} (hx : x ∈ nonzeroLocus σ) :
    x ∈ nonzeroLocus (DVR.secOfH0 σ) := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun a => congrArg j (Subsingleton.elim a 0)⟩
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have e := X.basicOpen_res (σ.f fun _ => i) (homOfLE (DVR.chart_le_weighted_chart_single (L := L) i)).op
  exact e.ge ⟨DVR.h0_le (fun _ => i) (X.basicOpen_le _ hj), hj⟩

theorem exists_section_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → CharZero R → ∀ (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal R) D A G), ∃ θ : LB.Sec U.LG.L, ∃ x ∈ nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint R := by
  intro R _ _ _ hN _ _ _ D A G _ _ hG U
  have : GeometricallyConnected G.hom := hG.geomConnected
  have hL := GlobalTheory.allSixLaws.1
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaCompare.exists_nonzero_closed hL.secBaseChange D.toPre
  obtain ⟨σ, fam, h0, hE, hm, -⟩ := GlobalTheory.ThetaUnit.exists_theta hL.globalFns hL.secBaseChange le_rfl U th hth
  obtain ⟨g, hg, hn⟩ := GlobalTheory.ThetaUnit.exists_mem_nonzeroLocus le_rfl U.toUnifPre (hE 0) (h0 ▸ hth) hm
  exact ⟨DVR.secOfH0 σ, g, nonzeroLocus_firstPower_section_subset σ hn, hg⟩

end GlobalTheory.ThetaClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.HermBlockChange.exists_unit_lower_block : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  intro O _ c h2 hcore n JL G G' hJL hdet hGG' hG
  obtain ⟨a, ha⟩ : ∃ a : O, a * 2 = 1 := ⟨↑(h2.unit⁻¹), by simp⟩
  have ha' : (2 : O) * a = 1 := by rw [mul_comm, ha]
  have hca : c a = a := by
    have h1 : c a * 2 = 1 := by
      have := congrArg c ha
      rwa [map_mul, map_one, map_ofNat] at this
    calc c a = c a * (2 * a) := by rw [ha', mul_one]
      _ = (c a * 2) * a := by ring
      _ = a := by rw [h1, one_mul]
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) 1 with hΔ
  set Nb : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1) with hNb
  set T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromCols Δ Nb with hTdef
  have hT : T = Matrix.fromBlocks 1 1 1 (-1) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [T, Δ, Nb]
  have hTt : Tᵀ = T := by
    rw [hT, Matrix.fromBlocks_transpose]; simp
  have hTc : T.map c = T := by
    rw [hT, Matrix.fromBlocks_map]; simp
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hTT : T * T = (2 : O) • 1 := by
    rw [hT, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]
  set J : Matrix (Fin n) (Fin n) O := (2 : O) • JL with hJ
  set K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks 0 J J 0 with hK
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks JL 0 0 (-JL) with hD
  have hTKT : T * K * T = (4 : O) • D := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp [J]
    exact ⟨by rw [← add_smul]; norm_num, by rw [← neg_add, ← add_smul]; norm_num⟩
  have hTDT : T * D * T = K := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [K, J, two_smul]
  have h4 : a * a * 4 = (1 : O) := by linear_combination (2 * a + 1) * ha
  set g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := a • (Tᵀ * G * T) with hg
  have hmapsmul : ∀ (b : O) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O), (b • M).map c = c b • M.map c := by
    intro b M; ext i j; simp
  have hgt : gᵀ = a • (T * Gᵀ * T) := by
    simp only [hg, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hTt, Matrix.mul_assoc]
  have hgc : g.map c = a • (T * G.map c * T) := by
    rw [hg, hTt, hmapsmul, Matrix.map_mul, Matrix.map_mul, hTc, hca]
  have hgK : gᵀ * K * g.map c = K := by
    rw [hgt, hgc]
    calc a • (T * Gᵀ * T) * K * a • (T * G.map c * T)
        = (a * a) • (T * Gᵀ * (T * K * T) * G.map c * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 4) • (T * (Gᵀ * D * G.map c) * T) := by
          rw [hTKT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = K := by rw [hG, h4, one_smul, hTDT]
  have hgdet : g * (a • (T * G' * T)) = 1 := by
    rw [hg, hTt]
    calc a • (T * G * T) * a • (T * G' * T)
        = (a * a) • (T * G * (T * T) * G' * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 2) • (T * (G * G') * T) := by
          rw [hTT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.one_mul]
      _ = 1 := by
          rw [hGG', Matrix.mul_one, hTT, smul_smul, show a * a * 2 * 2 = (1 : O) by linear_combination (2 * a + 1) * ha, one_smul]
  have hJherm : ∀ i j, c (J j i) = J i j := by intro i j; simp only [J, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat, hJL]
  have hJdet : IsUnit J.det := by
    rw [hJ, Matrix.det_smul]; exact (h2.pow _).mul hdet
  obtain ⟨Z, hZ1, hZ2⟩ := hcore n J hJherm hJdet g (Matrix.isUnit_det_of_right_inverse hgdet) hgK
  refine ⟨Z, ?_, ?_⟩
  · have h := congrArg (fun M => a • M) hZ1
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, ha, one_smul, smul_zero] at h
    exact h
  · have hblk : Tᵀ * G * T = Matrix.fromBlocks (Δᵀ * G * Δ) (Δᵀ * G * Nb) (Nbᵀ * G * Δ) (Nbᵀ * G * Nb) := by
      rw [hTdef, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    have h21 : g.toBlocks₂₁ = a • (Nbᵀ * G * Δ) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₁]
    have h22 : g.toBlocks₂₂ = a • (Nbᵀ * G * Nb) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₂]
    have hE : Nbᵀ * G * Nb + Nbᵀ * G * Δ * Z = (2 : O) • (g.toBlocks₂₁ * Z + g.toBlocks₂₂) := by
      rw [h21, h22, Matrix.smul_mul, ← smul_add, smul_smul, ha', one_smul, add_comm]
    rw [hE, Matrix.det_smul]; exact (h2.pow _).mul hZ2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.TateTransportAlg

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul_left hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

end GlobalTheory.TateTransportAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamRowsSizes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem famRowsSizes : ∀ {eps : ℝ} (Fm : FamP eps), TuSize Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, GlobalTheory.CoreHt.DelNat (Fm.D x i) → GlobalTheory.CoreHt.HtRowsS (Fm.L x i) Fm.CYL ∧ 8 ≤ (Fm.L x i).sc.X' ∧ 2 ≤ (Fm.L x i).sc.x ∧ (∀ u, 4 * (Fm.L x i).sc.a < (((Fm.D x i).mem u).A.T : ℝ)) ∧ ∀ u, Real.log ((((Fm.D x i).mem u).A.T : ℕ) : ℝ) ≤ max Fm.CTu 0 * (Fm.D x i).R.m * (Fm.L x i).sc.L := by
  intro eps Fm hTu
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x1, hT⟩ := hTu
  obtain ⟨xL, hL⟩ := GlobalTheory.scale_large_three eps he
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  obtain ⟨x4, h4⟩ := flipTwoThree.pow_le_exp_rpow_for_large_x 2 eps he
  refine ⟨max (max (max x1 xL) x3) (max x4 (max 9 (Fm.x1 + 1))), fun x hx i hDel => ?_⟩
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have eL : xL ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e9 : (9 : ℝ) ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  obtain ⟨hlog, h8, h2⟩ := hL (Fm.L x i).sc hse (by rw [hsx]; exact eL)
  have hThick : ThickUp (Fm.L x i) := fun j j1 j2 τ hc => ((Fm.L x i).win_thick j j1 j2 τ hc).2
  have hrows : HtRowsS (Fm.L x i) Fm.CYL := by
    have := GlobalTheory.CoreHt.RowsOfDesign.rows_of_design (Fm.D x i) (Fm.L x i) (Fm.params x e5 i) (Fm.sizes x e5 i) hlog hDel hThick
    rwa [Fm.params_CYL x e5 i] at this
  have hm : (4 : ℝ) ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; linarith)).1
    rw [hsx] at z1
    exact le_trans (h3 x e3) z1
  have hx0 : 0 < x := by linarith
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b; exact Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have h8b : 8 * x < (Fm.L x i).sc.b := by
    have hx2 := h4 x e4
    have hbe : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      unfold Scale.b Scale.L; rw [hsx, hse]
    rw [hbe]
    nlinarith
  have hb2 : (Fm.L x i).sc.b ^ (2 : ℝ) ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  rw [Real.rpow_two] at hb2
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := by linarith
  refine ⟨hrows, h8, h2, fun u => ?_, fun u => ?_⟩
  · have hTge := (hT x e1 i).1 u
    have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by unfold Scale.a; rw [hsx]
    rw [ha]
    have : 8 * (x * (Fm.L x i).sc.b) < (Fm.L x i).sc.b ^ 2 := by
      rw [← mul_assoc, sq]; exact mul_lt_mul_of_pos_right h8b hb0
    have hxb : 0 < x * (Fm.L x i).sc.b := mul_pos hx0 hb0
    linarith
  · refine le_trans ((hT x e1 i).2 u) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0) hL0

end GlobalTheory.CoreHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKottwitzClassesPerMinpolyAEqOneStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kottwitz_classes_per_minpoly_a_eq_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one) | (exact GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one) | (intros; apply GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompactStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_translates_smoothFunction_of_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsOpen {k | finRep E a k φ = φ} → ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S, finRep E a f φ = finRep E a f' φ := by
  first | exact @GlobalTheory.finite_translates_of_isCompact | exact GlobalTheory.finite_translates_of_isCompact | (intros; apply GlobalTheory.finite_translates_of_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogFinitePlaceEqNegLogAbsNorm
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.ProdFormula

theorem finsum_log_finitePlace_eq_neg_log_abs_norm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 →
      ∑ᶠ q : FinitePlace F, Real.log (q δ) = -Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
  intro F _ _ δ hδ
  have hpos : ∀ q : FinitePlace F, 0 < q δ := fun q => FinitePlace.pos_iff.2 hδ
  rw [← Real.log_finprod hpos, FinitePlace.prod_eq_inv_abs_norm hδ]
  push_cast
  rw [Real.log_inv]

end GlobalTheory.ProdFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightPositiveDiagonalLeSumAddInvStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  first | exact @GlobalTheory.height_diagonal_le_sum | exact GlobalTheory.height_diagonal_le_sum | (intros; apply GlobalTheory.height_diagonal_le_sum <;> assumption)
end

