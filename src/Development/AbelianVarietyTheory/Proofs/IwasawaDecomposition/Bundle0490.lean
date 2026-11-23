module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalAtPrimesUnitaryCongruentOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGalois
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReadingRationalAtTwistExtendsIntegralUnitar
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev.Approx

theorem underPl_conjP {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (P : HeightOneSpectrum (𝓞 E)) : underPl F (conjPrime₂ P) = underPl F P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [underPl_asIdeal, underPl_asIdeal, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, rll_cO_algebraMap hc]

theorem conjP_notMem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ1 : ∀ P : Q, conjPrime₂ P.1 ≠ P.1)
    (hQ2 : ∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') : ∀ P ∈ Q, conjPrime₂ P ∉ Q := by
  intro P hP hP'
  have h := hQ2 ⟨P, hP⟩ ⟨conjPrime₂ P, hP'⟩ (underPl_conjP hc P).symm
  exact hQ1 ⟨P, hP⟩ (congrArg Subtype.val h).symm

theorem red_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] (a : 𝓞 E) (ha : a ≠ 0) {u : GL (Fin n) (AfE F E)} (hu : u ∈ UAd hc n)
    (h : GlobalTheory.Mem.ColAd.CongOne a u) :
    ∃ hS : u ∈ St (1 : GL (Fin n) (AfE F E)), ∀ w : HeightOneSpectrum (𝓞 E), a ∈ w.asIdeal →
      redAt (1 : GL (Fin n) (AfE F E)) w ⟨u, hS⟩ = 1 := by
  classical
  have hca : Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) *
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by simpa using ha), map_one]
  have hs : ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j = (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j +
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) * (⟨_, h i j⟩ : Formalism.L2.Herm.intAf F E) := by
    intro i j
    show _ = _ + _ * (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ * _)
    rw [← mul_assoc, hca, one_mul]
    ring
  obtain ⟨s, hs⟩ : ∃ s : Fin n → Fin n → Formalism.L2.Herm.intAf F E, ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j + Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) * s i j :=
    ⟨fun i j => ⟨_, h i j⟩, hs⟩
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hi : ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E := by
    intro i j
    rw [hs]
    exact add_mem (hone i j) (mul_mem (iA_mem a) (s i j).2)
  have hSt := rlt_mem_St hc n hu hi
  obtain ⟨y, hy, hred⟩ := St_one_int hSt
  refine ⟨hSt, fun P hP => ?_⟩
  apply Units.ext
  ext i j
  rw [hred P i j]
  have e : y i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j + oToS F E a * s i j := by
    apply Subtype.ext
    rw [← hy, hs]
    simp only [Subring.coe_add, Subring.coe_mul]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  rw [e, map_add (f := _), map_mul, Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hP, zero_mul, add_zero]
  show _ = (1 : Matrix (Fin n) (Fin n) (kP P)) i j
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.SeeSaw.TwLev.Approx

namespace GlobalTheory.SeeSaw.TwLev.Approx

theorem rd_all : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {J : Matrix (Fin n) (Fin n) E}, J = 1 →
    ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ),
    (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → (∀ P P' : Q, underPl F P.1 = underPl F P'.1 → P = P') →
    (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F);
      ∀ᶠ (u : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1) →
    RdLevOn hc (RatAt Q) S.U S.chi Λ emb Q HQ lamQ →
    RdLevOn hc Set.univ S.U S.chi Λ emb Q HQ lamQ := by
  intro F E K _ _ _ _ _ _ _ hc n _ SG Q J hJ T f bad S Λ emb HQ lamQ hQ1 hQ2 hO hR
  subst hJ
  classical
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have hQc := conjP_notMem hc hQ1 hQ2
  have h1U : (1 : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) ∈
      {x : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} := S.U.one_mem
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype _ _ _).1 (S.U_open.mem_nhds h1U)
  obtain ⟨m₀, hm₀, hm₀N⟩ := GlobalTheory.T.congruenceOne_matrices_mem_nhds_one (F := F) (E := E) n (V ∩ {u | ∀ κ : S.U, κ.1 = u → S.chi κ = 1})
    (Filter.inter_mem hV hO)
  set m : ℕ := m₀ * ∏ w ∈ SG ∪ Q, Ideal.absNorm w.asIdeal with hm
  have hmpos : 0 < m := Nat.mul_pos hm₀ (Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot))
  have hmw : ∀ w ∈ SG ∪ Q, ((m : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    intro w hw
    obtain ⟨k, hk⟩ : Ideal.absNorm w.asIdeal ∣ m := Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hw) _
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  intro z _ hz hzU
  obtain ⟨g, hgU, hgR, hc1, hc2⟩ := _root_.GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne hc hQc m hmpos (fun P hP => hmw P (Finset.mem_union_right _ hP)) z hzU hz
  set u := z⁻¹ * g with hu
  have huU : u ∈ UAd hc n := mul_mem (inv_mem hzU) hgU
  have huN := hm₀N m (Dvd.intro _ rfl) hmpos u hc1 hc2
  have huS : u ∈ S.U := hVsub (a := ⟨u, huU⟩) huN.1
  have hchiu : S.chi ⟨u, huS⟩ = 1 := huN.2 ⟨u, huS⟩ rfl
  obtain ⟨huSt, hred⟩ := red_eq_one hc (m : 𝓞 E) (by exact_mod_cast hmpos.ne') huU hc1
  have hzg : g = z * u := by rw [hu, mul_inv_cancel_left]
  have hgSt : g ∈ St (1 : GL (Fin n) (AfE F E)) := hzg ▸ mul_mem hz huSt
  have hredg : ∀ w ∈ SG ∪ Q, redAt (1 : GL (Fin n) (AfE F E)) w ⟨g, hgSt⟩ = redAt 1 w ⟨z, hz⟩ := by
    intro w hw
    have e : (⟨g, hgSt⟩ : St (1 : GL (Fin n) (AfE F E))) = ⟨z, hz⟩ * ⟨u, huSt⟩ := Subtype.ext hzg
    rw [e, map_mul, hred w (hmw w hw), mul_one]
  obtain ⟨hiff, hchi⟩ := hR g hgR hgSt hgU
  have hgz : g ∈ S.U ↔ z ∈ S.U := by
    rw [hzg]
    exact ⟨fun h => by simpa using mul_mem h (inv_mem huS), fun h => mul_mem h huS⟩
  have hSGr : ∀ w : SG, redAt (1 : GL (Fin n) (AfE F E)) w.1 ⟨g, hgSt⟩ = redAt 1 w.1 ⟨z, hz⟩ :=
    fun w => hredg w.1 (Finset.mem_union_left _ w.2)
  have hQr : ∀ P : Q, redAt (1 : GL (Fin n) (AfE F E)) P.1 ⟨g, hgSt⟩ = redAt 1 P.1 ⟨z, hz⟩ :=
    fun P => hredg P.1 (Finset.mem_union_right _ P.2)
  refine ⟨?_, ?_⟩
  · rw [← hgz, hiff]
    simp only [hSGr, hQr]
  · intro hU h h'
    have hgU' : g ∈ S.U := hgz.2 hU
    have e1 := hchi hgU' (fun w => (hSGr w).symm ▸ h w) (fun P => (hQr P).symm ▸ h' P)
    have e2 : S.chi ⟨g, hgU'⟩ = S.chi ⟨z, hU⟩ := by
      have : (⟨g, hgU'⟩ : S.U) = ⟨z, hU⟩ * ⟨u, huS⟩ := Subtype.ext hzg
      rw [this, map_mul, hchiu, mul_one]
    rw [← e2, e1]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [show (⟨_, (hSGr w).symm ▸ h w⟩ : (Λ w).H) = ⟨_, h w⟩ from Subtype.ext (hSGr w)]
    · refine Finset.prod_congr rfl fun P _ => ?_
      rw [show (⟨_, (hQr P).symm ▸ h' P⟩ : HQ P) = ⟨_, h' P⟩ from Subtype.ext (hQr P)]

end GlobalTheory.SeeSaw.TwLev.Approx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqData
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThRead


set_option maxHeartbeats 1000000 in
theorem eW_jW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, ∀ y, Y.mj.eW i (Z.jW i y) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ _ i y
  exact (Z.jW_read i y).trans (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _))

theorem eW_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, Function.Injective (Y.mj.eW i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z _ _ i
  exact GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i)

theorem li_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, LinearIndependent ℂ (fun k => Z.jW i (Pi.single k 1)) ∧
    Submodule.span ℂ (Set.range fun k => Z.jW i (Pi.single k 1)) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i
  have he := eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hc : (Y.mj.eW i ∘ fun k => Z.jW i (Pi.single k 1)) = fun k =>
      GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1) :=
    funext fun k => eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i _
  refine ⟨LinearIndependent.of_comp (Y.mj.eW i) ?_, ?_⟩
  · rw [hc]; exact GlobalTheory.Mem.LiftTheta.goodForm_li R.toRealDat F.lv2 hH.prim.unif false i
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp, hc]
    exact (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
      ((hH.aux.levelW false i _).trans (Y.mj.eW_range i).symm)

theorem closure_span_eq {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V]
    [Module (𝓞 K) V] [AddCommGroup H] [Module ℂ H] (f : V →+ H) (hfs : ∀ (b : 𝓞 K) (x : V), f (b • x) = σ (b : K) • f x)
    (X : Set V) :
    AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' (Submodule.span (𝓞 K) X : Set V), y = σ (a : K) • x} := by
  set C := AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x}
  have stab : ∀ (b : 𝓞 K), ∀ z ∈ C, σ (b : K) • z ∈ C := by
    intro b z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨b * a, x, hx, by rw [smul_smul, ← map_mul]; norm_cast⟩
    | zero => rw [smul_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg _ _ h1 => rw [smul_neg]; exact C.neg_mem h1
  have key : ∀ x ∈ Submodule.span (𝓞 K) X, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure ⟨1, f x, ⟨x, hx, rfl⟩, by simp⟩
    | zero => rw [map_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact C.add_mem h1 h2
    | smul b x _ h => rw [hfs]; exact stab b _ h
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, _, ⟨x, Submodule.subset_span hx, rfl⟩, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [← hfs]
    exact key _ (Submodule.smul_mem _ a hx)

theorem chiKs_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m, (R.FW i).ChiKs := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩


set_option maxHeartbeats 1000000 in
theorem lat_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ i : Fin D.R.m,
    OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (Z.jW i) ((A3.indefDown (s0Of R F)).M i) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i
  have he := eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hli := (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).1
  have hej := eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  have hI := hH.aux.integral i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1)
    (chiKs_of_pins D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i) F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
    (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]; rfl⟩
  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have himg : Y.mj.eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier =
      (R.FW i).j (sg0 D A3.A) '' {y | y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy1, hy2, e⟩ := (Y.mj.eW_lat i x).1 hx
      exact ⟨y, ⟨hy1, hy2⟩, e.symm⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyM : y ∈ (R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
        rw [← hspan]; exact Submodule.subset_span ⟨hy1, hy2⟩
      obtain ⟨c, -, hcy⟩ := (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i _).1 ⟨y, hyM, rfl⟩
      exact ⟨Z.jW i c, (Y.mj.eW_lat i _).2 ⟨y, hy1, hy2, (hej c).trans hcy⟩, (hej c).trans hcy⟩
  refine GlobalTheory.Mem.LiftTheta.oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (Y.mj.eW i) he (Z.jW i)
    (GlobalTheory.Mem.LiftTheta.semi_injective _ hli) _
    ((R.FW i).j (sg0 D A3.A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) : Set _)) (fun y => ?_) ?_
  · refine (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i y).trans ?_
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).trans h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).symm.trans h⟩⟩
  · rw [himg, ← hspan]
    exact closure_span_eq (σ := D.what₂.embLL) ((R.FW i).j (sg0 D A3.A)).toAddMonoidHom
      (fun b x => by
        rw [← hsg]
        show (R.FW i).j _ (b • x) = _
        rw [← algebraMap_smul D.what₂.LL b x, map_smulₛₗ]
        rfl) _


set_option maxHeartbeats 2000000 in
theorem theta_of (T1 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) x, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x))) (T2 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0) : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ∀ (i : Fin D.R.m) (t : T) x,
    D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
      Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t x
  change Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL at x
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h5 := hR.lifts0.1
  have hr := hR.ratTh
  have hOk := hH.ok.ok2
  apply eW_injective D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i
  refine (T1 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t x).trans ?_
  refine Eq.trans ?_ (eW_jW D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i _).symm
  have hp : Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) := BlockDat.lf_l_proj ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hsub : ∀ a b, liftForm A3.A F.P0 F.ψ0 i t (a - b) = liftForm A3.A F.P0 F.ψ0 i t a - liftForm A3.A F.P0 F.ψ0 i t b :=
    fun a b => by unfold liftForm; rw [Matrix.mulVec_sub, map_sub]
  have h1 : R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t
      (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)))) := by
    have h := T2 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t
      (x - lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)) (fun z => by rw [map_sub, GlobalTheory.Mem.LiftForms.hform_orth hp, sub_self])
    rwa [hsub, map_sub, map_sub, sub_eq_zero] at h
  rw [h1]
  have h2 := GlobalTheory.Mem.LiftTheta.liftMatrix_computes_lift_rational (R.toCx3 F) F.cr false h5 hr i t
    (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)
  have h3 := GlobalTheory.Mem.LiftTheta.levelFormCoordinateMap_levelZero F.lv2 hOk (A3.fam3.toSub2 (zsOf R F)) i t
    (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)
  have h4 := GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i
    ((R.toCx3 F).liftMat F.cr false i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
  have key := h4.symm.trans (h2.trans (by
    show R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) _) = _
    have h3' : F.cr.toL (R.toCx3 F).zs false i t (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x) =
        LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P (A3.A.fam.lvlA F.P0 F.ψ0).ψ
          (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x)) :=
      h3.symm
    rw [hP.phs i, one_smul, h3']
    rfl))
  exact (congrArg Tw.out key).symm


set_option maxHeartbeats 1000000 in
theorem thDef3_thTheta : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →  ThDef3 D A3.A (A3.indefDown (s0Of R F)) Y.tup Y.eMt Z.jW ∧ ∀ (i : Fin D.R.m) (t : T) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) = Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  exact ⟨⟨fun i => (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).1,
    fun i => (li_span D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i).2, lat_of D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH⟩,
    theta_of GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree GlobalTheory.T.liftLevelForm_orthogonal_killed_by_thetaMap D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH⟩

end GlobalTheory.Mem.ThRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelSame
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult

namespace GlobalTheory.Mem.R3.Rw.GeoTies

def ModelSame {D D' : D7} {V : HSp D} {V' : HSp D'} {S : D.what₂.Tau → SPar} {S' : D'.what₂.Tau → SPar}
    (M : DSModel V S) (M' : DSModel V' S') : Prop :=
  HEq M'.H M.H ∧ HEq M'.nacg M.nacg ∧ HEq M'.ips M.ips ∧ HEq M'.σ M.σ ∧ HEq M'.lam M.lam ∧ HEq M'.ε M.ε ∧ HEq M'.fr M.fr

section Two

variable {D D' : D7} {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {A' : FamIn D'.what₂.LL G' Pl0' T0' D'.R.m}

def MWOver {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' D'.what₂.LL]
    (R : RealDat D A Ks) (R' : RealDat D' A' Ks') : Prop :=
  ∀ (i : Fin D.R.m) (i' : Fin D'.R.m), (i : ℕ) = i' → ∀ ι : D.what₂.LL →+* D'.what₂.LL, (∀ x, D'.what₂.embLL (ι x) = D.what₂.embLL x) →
    ∀ σ' : D'.what₂.LL →+* ℂ, ModelSame (R.MW i (σ'.comp ι)) (R'.MW i' σ')

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  {C' : Formalism.L2.Pj.Core D'} [Algebra C'.Q.c.F D'.what₂.LL] {R' : RealDat D' A' C'.Q.c.F} {i' : Fin D'.R.m}

def OmOver (O : OMDat C R i Unit (fun _ => A.μ0)) (O' : OMDat C' R' i' Unit (fun _ => A'.μ0)) : Prop :=
  HEq O'.lev O.lev ∧ ∃ (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F), HEq O'.c' c ∧
    ∀ h J, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) →
      ∃ h' J', RepsR R' i' A'.μ0 h' (O'.bad ()) J' (O'.Lh ()) (O'.gam ()) (O'.vol ()) ∧
        ∀ (x₀ : A.fam.amb.FL i A.μ0) (x : O.Cl' () → VsV D i O.c'.F), Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x →
          ∀ y' : (R'.HV i' A'.μ0).H, HEq y' (jVx R i A.μ0 x₀) →
            ∃ x' : O'.Cl' () → VsV D' i' O'.c'.F, Place R' i' A'.μ0 h' O'.c0' y' x' ∧
              ∀ a n, ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' a n, GlobalTheory.OneMapAll.IsSum O () x f →
                ∀ f' : Rul (C'.Q.Xo ((i' : ℕ) + 1)) O'.c', HEq f' (GlobalTheory.FieldBC.rulBC hle f) → GlobalTheory.OneMapAll.IsSum O' () x' f'

end Two

end GlobalTheory.Mem.R3.Rw.GeoTies

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
section
noncomputable section

namespace GlobalTheory.PtSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

theorem map_MjSig_eq (D : D7) (i : D.nd.Loc) (hInt : Rows.IsotInternal D.what₂) (h42 : SumRepresentations.At.Conclusion42 D.nd D.naut i)
    (hUp : ParUpRec D.nd D.naut i) (hDown : DownMemRec D.nd D.naut i) (hNZ : TypeNZRec D.nd D.naut i) :
    ∀ x ∈ ZgoodN D.nd D.naut i, ∀ Sig, HasParamX D.nd D.naut i x Sig →
      (MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = eigC D.nd D.naut i x := by
  intro x hx Sig hS
  refine Submodule.eq_of_le_of_finrank_le (hUp x hx Sig hS) ?_
  have hinj := SumRepresentations.thetaT_injective D.nd D.naut i hInt h42
  have h1 : Module.finrank ℂ ↥((MjSig D.nd D.naut i Sig).map (D.what₂.thetaT (D.nd.mu i) (D.nd.j i))) =
      Module.finrank ℂ ↥(MjSig D.nd D.naut i Sig) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (MjSig D.nd D.naut i Sig))).symm
  have hfi : Function.Injective ((D.what₂.thetaP (D.nd.mu i) (D.nd.j i)).domRestrict (eigC D.nd D.naut i x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    exact Subtype.ext (hNZ x hx F.1 F.2 hF)
  have h2 : Module.finrank ℂ ↥(eigC D.nd D.naut i x) =
      Module.finrank ℂ ↥((eigC D.nd D.naut i x).map (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))) := by
    rw [← LinearMap.range_domRestrict]
    exact (LinearMap.finrank_range_of_inj hfi).symm
  rw [h1, h2]
  exact Submodule.finrank_mono (hDown x hx Sig hS)

end GlobalTheory.PtSt

end
end

