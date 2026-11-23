module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CommonDenom
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ProdEP2Uni

section LocTop

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem topE (M : Loc.Model F E) : IsTopologicalRing E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  first
    | exact IsModuleTopology.isTopologicalRing F E
    | exact IsModuleTopology.topologicalRing F E

theorem t2E (M : Loc.Model F E) : T2Space E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  let b := Module.Free.chooseBasis F E
  have hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F)) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

theorem int_mem {x : F} (h : IsIntegral 𝒪[F] x) : x ∈ 𝒪[F] := by
  first
    | exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
    | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
       rw [← hy]
       exact y.2)

theorem alg_int (x : 𝒪[F]) : algebraMap F E (x : F) = algebraMap 𝒪[F] E x := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm

private theorem R_eq_O_of_split_eq_none (M : Loc.Model F E) (hg : M.split = none) : M.R = M.L.O := by
  simp only [Loc.Model.R, hg]

private theorem mem_R_iff_of_split_eq_some (M : Loc.Model F E) (g : Loc.SplitG M.L) (hg : M.split = some g) (z : E) :
    z ∈ M.R ↔ ∃ a b : 𝒪[F], g.e z = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  simp only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩

theorem alg_mem_R (M : Loc.Model F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ M.R := by
  cases hg : M.split with
  | none =>
    rw [R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]
    exact isIntegral_algebraMap
  | some g =>
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨a, a, ?_, rfl⟩
    rw [AlgEquiv.commutes]
    first
      | rfl
      | simp

private theorem splitG_e_mem_integers_of_mem_O (L : Loc.LocE F E) (g : Loc.SplitG L) {z : E} (hz : z ∈ L.O) :
    (g.e z).1 ∈ 𝒪[F] ∧ (g.e z).2 ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (g.e z) := ((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])),
    int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩

private theorem mem_O_of_mem_R (M : Loc.Model F E) {z : E} (hz : z ∈ M.R) : z ∈ M.L.O := by
  cases hg : M.split with
  | none =>
    rwa [R_eq_O_of_split_eq_none M hg] at hz
  | some g =>
    obtain ⟨a, b, he, -⟩ := (mem_R_iff_of_split_eq_some M g hg z).mp hz
    rw [M.L.O_def]
    have ha : IsIntegral 𝒪[F] (a : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))
    have hb : IsIntegral 𝒪[F] (b : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))
    have h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F) := IsIntegral.pair ha hb
    have h2 := h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
    rw [← he] at h2
    have e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z := g.e.symm_apply_apply z
    rwa [e] at h2

theorem R_compact [CharZero F] (M : Loc.Model F E) : IsCompact (M.R : Set E) := by
  haveI := topE M
  have hO := (MainNotions.LocalModelPeriodLattices.O_top M.L).2.1
  have hRo : IsOpen (M.R : Set E) := PI.ProdFormulaE.ROpen.isOpen_R M
  have hRc : IsClosed (M.R : Set E) := M.R.toAddSubgroup.isClosed_of_isOpen hRo
  exact hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)

theorem R_denom (M : Loc.Model F E) (y : E) : ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E (a : F) * y ∈ M.R := by
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  haveI : Nontrivial E := by
    first
      | exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
      | exact Module.nontrivial_of_finrank_eq_succ M.L.rank
  haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)
  have hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0 := by
    intro x hx
    rw [← alg_int] at hx
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)
  have halg : IsAlgebraic 𝒪[F] y := by
    have hF : IsAlgebraic F y := (Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF
  have hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y) := by
    first
      | (obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj
         exact ⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)
      | (obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple
         exact ⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)
  obtain ⟨s, hs, hsi⟩ := hex
  have hsy : algebraMap F E (s : F) * y ∈ M.L.O := by
    rw [M.L.O_def, alg_int]
    exact hsi
  cases hg : M.split with
  | none =>
    exact ⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩
  | some g =>
    refine ⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩
    obtain ⟨h1, h2⟩ := splitG_e_mem_integers_of_mem_O M.L g hsy
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩
    · have e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y =
          algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y) := by
        rw [MulMemClass.coe_mul, map_mul, mul_assoc]
      rw [e, map_mul, AlgEquiv.commutes]
      ext <;> simp
    · have hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0 := fun t =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))
      rw [hq, hq]

theorem common_denom (M : Loc.Model F E) {ι : Type} [Fintype ι] (y : ι → E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ k, algebraMap F E (a : F) * y k ∈ M.R := by
  classical
  choose d hd0 hd using fun k => R_denom M (y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  have hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm
  rw [hp]
  have e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k =
      algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k) := by
    rw [MulMemClass.coe_mul, map_mul, mul_assoc]
  rw [e]
  exact M.R.mul_mem (alg_mem_R M _) (hd k)

end LocTop

end Formalism.L2.SG.Pf.ProdEP2Uni
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensCongPf
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel

section Act

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι]

def act (A : Matrix ι ι E) (v : ι → V) : ι → V := fun b => ∑ a, A a b • v a

theorem act_act (A B : Matrix ι ι E) (v : ι → V) : act A (act B v) = act (B * A) v := by
  funext b
  simp only [act, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

theorem h_sum_left {κ : Type} (s : Finset κ) (f : κ → V) (y : V) : H.h (∑ c ∈ s, f c) y = ∑ c ∈ s, H.h (f c) y := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact H.h_zero_left y
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, H.h_add_left, ih]

theorem h_right (x y : V) : H.h x y = M.L.cj (H.h y x) := by
  rw [H.h_herm x y, M.L.cj_cj]

theorem h_sum_right {κ : Type} (s : Finset κ) (f : κ → V) (x : V) : H.h x (∑ c ∈ s, f c) = ∑ c ∈ s, H.h x (f c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h_right, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun c _ => (h_right H x (f c)).symm

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [h_right, H.h_smul_left, map_mul, ← h_right]

theorem gram_act (A : Matrix ι ι E) (v : ι → V) (a b : ι) :
    H.h (act A v b) (act A v a) =
      ((A.map M.L.cj).transpose * Matrix.of (fun c d => H.h (v d) (v c)) * A) a b := by
  simp only [act, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  rw [h_sum_left]
  simp only [H.h_smul_left, h_sum_right, h_smul_right, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

end Act

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem act_one (v : ι → V) : act (1 : Matrix ι ι E) v = v := by
  funext b
  simp only [act, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem o_mul_mem (S : Submodule M.L.O E) {o x : E} (ho : o ∈ M.L.O) (hx : x ∈ S) : o * x ∈ S :=
  S.smul_mem ⟨o, ho⟩ hx

theorem cong_act (S : Submodule M.L.O E) (A G : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a b, H.h (v b) (v a) - G a b ∈ S) :
    ∀ a b, H.h (act A v b) (act A v a) - ((A.map M.L.cj).transpose * G * A) a b ∈ S := by
  intro a b
  rw [gram_act, ← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.of_apply]
  refine S.sum_mem fun c _ => ?_
  rw [Finset.sum_mul]
  refine S.sum_mem fun d _ => ?_
  rw [mul_comm _ (A c b), ← mul_assoc]
  rw [mul_comm (A c b)]
  refine o_mul_mem S (Subring.mul_mem _ (Formalism.MainNotions.LocalModelPeriodLattices.cj_mem_O M.L _ (hAO d a)) (hAO c b)) (hv d c)

theorem mem_lam_act (abelian₂ : Submodule M.L.O V) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V)
    (hv : ∀ a, v a ∈ abelian₂) (b : ι) : act A v b ∈ abelian₂ :=
  abelian₂.sum_mem fun a _ => abelian₂.smul_mem ⟨A a b, hAO a b⟩ (hv a)

theorem mem_span_act (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span M.L.O (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (⟨A a b, hAO a b⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)

theorem mem_spanE_act (A : Matrix ι ι E) (v : ι → V) (b : ι) :
    act A v b ∈ Submodule.span E (Set.range v) :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ (A a b) (Submodule.subset_span ⟨a, rfl⟩)

theorem prim_act (abelian₂ : Submodule M.L.O V) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (hBA : B * A = 1) (v : ι → V) (hv : H.Prim abelian₂ v) :
    H.Prim abelian₂ (act A v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hback : act B (act A v) = v := by rw [act_act, hAB, act_one]
  refine ⟨mem_lam_act abelian₂ A hAO v h1, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at h2 ⊢
    intro g hg
    have e : ∑ b, g b • act A v b = ∑ a, (A *ᵥ g) a • v a := by
      simp only [act, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [e] at hg
    have h0 := h2 _ hg
    have hAg : A *ᵥ g = 0 := funext h0
    have : g = B *ᵥ (A *ᵥ g) := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    intro b
    rw [this, hAg, Matrix.mulVec_zero]
    rfl
  · intro x hx hxs
    have hxv : x ∈ Submodule.span E (Set.range v) := by
      refine Submodule.span_le.2 ?_ hxs
      rintro _ ⟨b, rfl⟩
      exact mem_spanE_act A v b
    have hO := h3 x hx hxv
    refine Submodule.span_le.2 ?_ hO
    rintro _ ⟨a, rfl⟩
    have : v a = act B (act A v) a := by rw [hback]
    rw [SetLike.mem_coe, this]
    exact mem_span_act B hBO (act A v) a

end Main

end Formalism.L2.SG.Pf.DensCongPf

namespace Formalism.L2.SG.Pf.DensCongPf

open Formalism.MainNotions.S ValuativeRel
open scoped Matrix

section Count

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  (H : Loc.HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem det_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : A.det ∈ M.L.O := by
  rw [Matrix.det_apply]
  exact M.L.O.sum_mem fun σ _ => Subring.zsmul_mem _ (M.L.O.prod_mem fun i _ => hA _ _) _

theorem adj_mem (A : Matrix ι ι E) (hA : ∀ i j, A i j ∈ M.L.O) : ∀ i j, A.adjugate i j ∈ M.L.O := by
  intro i j
  rw [Matrix.adjugate_apply]
  refine det_mem _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs; exacts [M.L.O.one_mem, M.L.O.zero_mem]
  · exact hA a b

def cls (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) (G₀ : Matrix ι ι E) :
    Set (ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) abelian₂) :=
  Set.range fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
    fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)

def psi (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (x : ι → V ⧸ H.smulLat c abelian₂) : ι → V ⧸ H.smulLat c abelian₂ :=
  fun b => ∑ a, (⟨A a b, hAO a b⟩ : M.L.O) • x a

theorem psi_mk (abelian₂ : Submodule M.L.O V) (c : E) (A : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O) (v : ι → V) :
    psi H abelian₂ c A hAO (fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (v a)) =
      fun a => Submodule.Quotient.mk (p := H.smulLat c abelian₂) (act A v a) := by
  funext b
  simp only [psi, act]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (Submodule.Quotient.mk (∑ a, A a b • v a) : V ⧸ H.smulLat c abelian₂) =
    (H.smulLat c abelian₂).mkQ (∑ a, A a b • v a) from rfl, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show _ = (H.smulLat c abelian₂).mkQ ((⟨A a b, hAO a b⟩ : M.L.O) • v a)
  rw [LinearMap.map_smul]
  rfl

theorem psi_psi (abelian₂ : Submodule M.L.O V) (c : E) (A B : Matrix ι ι E) (hAO : ∀ i j, A i j ∈ M.L.O)
    (hBO : ∀ i j, B i j ∈ M.L.O) (hAB : A * B = 1) (x : ι → V ⧸ H.smulLat c abelian₂) :
    psi H abelian₂ c B hBO (psi H abelian₂ c A hAO x) = x := by
  funext b
  simp only [psi, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ a, ∑ y, ((⟨B y b, hBO y b⟩ : M.L.O) * ⟨A a y, hAO a y⟩) • x a =
      (if a = b then (1 : M.L.O) else 0) • x a := by
    intro a
    rw [← Finset.sum_smul]
    congr 1
    apply Subtype.ext
    have h := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at h
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rw [Finset.sum_congr rfl (fun y _ => mul_comm (B y b) (A a y)), h, Matrix.one_apply]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp

end Count

end Formalism.L2.SG.Pf.DensCongPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExistsOfMemSmulLat
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem exists_of_mem_smulLat {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {c : E} {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) : ∃ l ∈ abelian₂, x = c • l := by
  unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨l, hl, rfl⟩
  | zero => exact ⟨0, abelian₂.zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨l + m, abelian₂.add_mem hl hm, by simp [smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨a • l, abelian₂.smul_mem a hl, smul_comm a c l⟩

def Lemma0G (M : Model F E) (r : ℕ) : Prop :=
  ∀ g : SplitG M.L, M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f' ∧
        (H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) ∈ H.iotaGraph g t))

theorem lemma0G_holds (M : Model F E) (r : ℕ) : Lemma0G M r := by
  intro g hg V _ _ H t hgen w hw
  constructor
  · intro hwL
    refine ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩, ?_⟩
    refine ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, hwL, ?_, rfl⟩
    simp only [sub_self]
    exact Submodule.zero_mem _
  · rintro ⟨-, -, x', x, hx'L, hxL, hxx, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [HermSp.mkW, Submodule.mkQ_apply] at hp1 hp2

    have ha' : w - (x' : V) ∈ H.X t.f' := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp1
    have ha : w - (x : V) ∈ H.X t.f := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp2
    obtain ⟨α', hα'⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha'
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha
    obtain ⟨l, hl, hxl⟩ := exists_of_mem_smulLat H hxx
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (by exact_mod_cast h0)
    have hqqi : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
    have hqiq : algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
      rw [mul_comm, hqqi]
    have hMM : H.MMfam t =
        Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      simp only [HermSp.MMfam, hg]
    obtain ⟨-, hli, hprim⟩ := hgen.2
    rw [hMM] at hli hprim

    let γ : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim
      (Fin.snoc (fun i => algebraMap F E ((g.q : F)⁻¹) * (α' i - α i)) 0) (Fin.snoc α' 0)
    have hsum : ∑ j, γ j • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      have key : algebraMap F E (g.q : F) • ∑ j, γ j • Sum.elim t.f
          (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j =
          algebraMap F E (g.q : F) • l := by
        rw [← hxl, Fintype.sum_sum_type]
        simp only [γ, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, smul_add, Finset.smul_sum]
        have e1 : (x : V) - x' = (w - x') - (w - x) := by abel
        rw [e1, ← hα', ← hα, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← mul_assoc, hqqi, one_mul, smul_comm (algebraMap F E (g.q : F)) (α' i),
          smul_smul (algebraMap F E (g.q : F)), hqqi, one_smul, sub_smul, smul_sub]
        abel
      calc _ = (algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F)) • ∑ j, γ j • Sum.elim t.f
              (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j := by
            rw [hqiq, one_smul]
        _ = l := by rw [mul_smul, key, ← mul_smul, hqiq, one_smul]
    have hlO := hprim l hl ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨γ, hsum⟩)
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hlO
    have hβ' : ∑ j, (β j : E) • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      simpa only [Subring.smul_def] using hβ
    have hzero := Fintype.linearIndependent_iff.1 hli (fun j => (β j : E) - γ j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hβ', hsum, sub_self])

    have hmem : ∀ i : Fin r, α' i ∈ M.L.O := by
      intro i
      have := hzero (Sum.inr i.castSucc)
      simp only [γ, Sum.elim_inr, Fin.snoc_castSucc, sub_eq_zero] at this
      rw [← this]
      exact (β _).2
    have hf'L := hgen.1.2.2.1.1.1
    have hw' : w = (x' : V) + ∑ i, α' i • t.f' i.castSucc := by rw [hα']; abel
    rw [hw']
    refine t.abelian₂.add_mem hx'L (Submodule.sum_mem _ fun i _ => ?_)
    have := t.abelian₂.smul_mem (⟨α' i, hmem i⟩ : M.L.O) (hf'L i.castSucc)
    simpa only [Subring.smul_def] using this

end G

end Formalism.L2.SG.LsDatumA
end
end

