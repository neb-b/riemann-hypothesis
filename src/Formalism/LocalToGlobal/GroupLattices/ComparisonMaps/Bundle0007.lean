module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0004
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.Bundle0008

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsGat
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)


include hH in
theorem class_eq_iff_translate_level_one (i i' : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y = (repP L p i).1) (Lt Lt' : Fin nV → Submodule W (Fin (m + 1) → Qq))
    (h : ∀ v, IsLattice W (Lt v)) (h' : ∀ v, IsLattice W (Lt' v)) :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y,
        Lt' = (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt := by
  simp only [level_action_lattice_eq]
  subst hy
  exact class_eq_iff_translate_level_zero hk I hdet hH i i' Lt Lt' h h'


set_option maxHeartbeats 2000000 in
include hH in
theorem clsC_iff (i i' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp)
    (Lt Lt' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup)
    (h : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt)
    (h' : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt') :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).Γ,
        Lt' = ((gatOfLevelP L hS nV r lam0 dom hk I ψ e).lev i).smul γ Lt :=
  class_eq_iff_translate_level_one hS r lam0 dom hk I ψ hdet hH i i' _ rfl Lt Lt' h h'


include hH in
theorem clsC_surj (c : ClassSet (HA sp) (KA L)) :
    ∃ (i : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).comp) (Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup),
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt ∧ clsC I hdet hk i Lt = c := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  obtain ⟨i, g, hg⟩ := (fibP I hdet hk hH).cls_surj (HA sp) (repP L p)
    (repP_mk L p) x (repP_mk L p)
  exact ⟨i, tupOf W g, tupOf_lat W g, (clsC_tupOf I hdet hk hH i g).trans hg⟩


include hH hdet in
theorem finClasses : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).FinClasses := by
  intro i
  have := finite_classSet_U L
  let f : {Lt : (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup //
      (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.IsLatTup Lt} → ClassSet (HA sp) (KA L) :=
    fun Lt => clsC I hdet hk i Lt.1
  let s : Set.range f → (gatOfLevelP L hS nV r lam0 dom hk I ψ e).P.Tup := fun c => (Classical.choose c.2).1
  have hs : ∀ c : Set.range f, f (Classical.choose c.2) = c.1 := fun c => Classical.choose_spec c.2
  refine ⟨(Set.finite_range s).toFinset, ?_, ?_⟩
  · intro L0 hL0
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hL0
    exact (Classical.choose c.2).2
  · intro Lt hLt
    let c : Set.range f := ⟨f ⟨Lt, hLt⟩, Set.mem_range_self _⟩
    refine ⟨s c, (Set.Finite.mem_toFinset _).2 ⟨c, rfl⟩, ?_⟩
    exact ((clsC_iff hS r lam0 dom hk I ψ e hdet hH i i (s c) Lt (Classical.choose c.2).2 hLt).1 (hs c)).2

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.HRatInvOfTriv
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def InvAt (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) : Prop :=
  ∀ γ : (G.lev i).Γ, (G.lev i).smul γ L0 = L0 → ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ = ξ

def HRatInv : Prop :=
  ∀ (i : G.comp) (L0 : G.P.Tup), G.P.IsLatTup L0 →
    {ξ | ξ ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ} ⊆
      Submodule.span G.O {ξ | ξ ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ ∧ RatX G e ξ}

theorem chiAct_mul (i : G.comp) (a b : (G.lev i).Γ) (ξ : G.P.Xsp) :
    ((G.lev i).χ (a * b) : G.O) • (G.lev i).actX (a * b) ξ =
      ((G.lev i).χ a : G.O) • (G.lev i).actX a (((G.lev i).χ b : G.O) • (G.lev i).actX b ξ) := by
  rw [map_mul, Units.val_mul, Formalism.MainNotions.G.LatticeSystems.jd_actX_mul, LinearMap.comp_apply, LinearMap.map_smul_of_tower, smul_smul]

theorem jdI_apply (i : G.comp) (L0 : G.P.Tup) (γ : (G.lev i).Γ) (ξ : G.P.Xsp) (hξ : InvAt G i L0 ξ) :
    delta G i L0 ξ i ((G.lev i).smul γ L0) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ := by
  classical
  unfold Formalism.MainNotions.G.LatticeSystems.delta
  have hex : ∃ γ' : (G.lev i).Γ, (G.lev i).smul γ L0 = (G.lev i).smul γ' L0 := ⟨γ, rfl⟩
  rw [dite_eq_left hex, if_pos rfl]
  have hspec : (G.lev i).smul γ L0 = (G.lev i).smul hex.choose L0 := hex.choose_spec
  have hstab : (G.lev i).smul (γ⁻¹ * hex.choose) L0 = L0 := by
    rw [Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, ← hspec, ← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, inv_mul_cancel,
      Formalism.MainNotions.G.LatticeSystems.jd_smul_one]
  have h1 := hξ (γ⁻¹ * hex.choose) hstab
  calc ((G.lev i).χ hex.choose : G.O) • (G.lev i).actX hex.choose ξ
      = ((G.lev i).χ (γ * (γ⁻¹ * hex.choose)) : G.O) • (G.lev i).actX (γ * (γ⁻¹ * hex.choose)) ξ := by
        rw [mul_inv_cancel_left]
    _ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (((G.lev i).χ (γ⁻¹ * hex.choose) : G.O) •
          (G.lev i).actX (γ⁻¹ * hex.choose) ξ) := chiAct_mul G i _ _ ξ
    _ = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ := by rw [h1]

theorem jdI_mem (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (hE : EquivSys G Hv)
    (i : G.comp) (L0 : G.P.Tup) (hL0 : G.P.IsLatTup L0) (ξ : G.P.Xsp) (hξ : ξ ∈ Hv L0) (hI : InvAt G i L0 ξ) :
    delta G i L0 ξ ∈ G.funMod Hv := by
  classical
  rw [Formalism.MainNotions.G.GAtP.funMod, Submodule.mem_pi]
  intro i' _
  unfold Formalism.MainNotions.G.Level.funMod
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Submodule.mem_iInf]
    intro L
    rw [Submodule.mem_iInf]
    intro hL
    rw [Submodule.mem_comap, LinearMap.proj_apply]
    unfold Formalism.MainNotions.G.LatticeSystems.delta
    split_ifs with h1 h2
    · have h3 := hE i h1.choose L0 hL0 ξ hξ
      rwa [← h1.choose_spec] at h3
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
  · rw [Submodule.mem_iInf]
    intro L
    rw [Submodule.mem_iInf]
    intro hL
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    apply Formalism.MainNotions.G.LatticeSystems.jd_zero
    right
    rintro ⟨γ, rfl⟩
    exact hL (Formalism.MainNotions.G.LatticeSystems.jd_lat _ γ L0 hL0)
  · rw [Submodule.mem_iInf]
    intro γ
    rw [Submodule.mem_iInf]
    intro L
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp only [LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply]
    by_cases hi : i' = i
    · subst hi
      by_cases hL : ∃ h : (G.lev i').Γ, L = (G.lev i').smul h L0
      · obtain ⟨h, rfl⟩ := hL
        rw [← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, jdI_apply G i' L0 _ ξ hI, jdI_apply G i' L0 h ξ hI, chiAct_mul]
      · have hL' : ¬ ∃ h : (G.lev i').Γ, (G.lev i').smul γ L = (G.lev i').smul h L0 := by
          rintro ⟨h, hh⟩
          apply hL
          refine ⟨γ⁻¹ * h, ?_⟩
          rw [Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, ← hh, ← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, inv_mul_cancel,
            Formalism.MainNotions.G.LatticeSystems.jd_smul_one]
        rw [Formalism.MainNotions.G.LatticeSystems.jd_zero G i' L0 ξ i' _ (Or.inr hL'),
          Formalism.MainNotions.G.LatticeSystems.jd_zero G i' L0 ξ i' _ (Or.inr hL), map_zero, smul_zero]
    · rw [Formalism.MainNotions.G.LatticeSystems.jd_zero G i L0 ξ i' _ (Or.inl hi), Formalism.MainNotions.G.LatticeSystems.jd_zero G i L0 ξ i' _ (Or.inl hi),
        map_zero, smul_zero]

theorem inv_of_mem (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) (hF : F ∈ G.funMod Hv) (i : G.comp)
    (L0 : G.P.Tup) : InvAt G i L0 (F i L0) := by
  intro γ hγ
  have hFi : F i ∈ (G.lev i).funMod Hv := (Submodule.mem_pi.mp hF) i (Set.mem_univ i)
  unfold Formalism.MainNotions.G.Level.funMod at hFi
  rw [Submodule.mem_inf, Submodule.mem_inf] at hFi
  have h3 := hFi.2
  rw [Submodule.mem_iInf] at h3
  have h4 := h3 γ
  rw [Submodule.mem_iInf] at h4
  have h5 := h4 L0
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h5
  simp only [LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.restrictScalars_apply] at h5
  rw [hγ] at h5
  exact h5.symm

theorem jdI_decomp (reps : Finset (G.comp × G.P.Tup)) (hR : IsReps G reps)
    (Hv : G.P.Tup → Submodule G.O G.P.Xsp) (F : G.Fn) (hF : F ∈ G.funMod Hv) :
    F = ∑ r ∈ reps, delta G r.1 r.2 (F r.1 r.2) := by
  classical
  have hcomp : ∀ i, F i ∈ (G.lev i).funMod Hv := fun i => (Submodule.mem_pi.mp hF) i (Set.mem_univ i)
  have heqv : ∀ (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup),
      F i ((G.lev i).smul γ L) = ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (F i L) := by
    intro i γ L
    have hFi := hcomp i
    unfold Formalism.MainNotions.G.Level.funMod at hFi
    rw [Submodule.mem_inf, Submodule.mem_inf] at hFi
    have h3 := hFi.2
    rw [Submodule.mem_iInf] at h3
    have h4 := h3 γ
    rw [Submodule.mem_iInf] at h4
    have h5 := h4 L
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h5
    simpa only [LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply] using h5
  have hzero : ∀ (i : G.comp) (L : G.P.Tup), ¬ G.P.IsLatTup L → F i L = 0 := by
    intro i L hL
    have hFi := hcomp i
    unfold Formalism.MainNotions.G.Level.funMod at hFi
    rw [Submodule.mem_inf, Submodule.mem_inf] at hFi
    have h3 := hFi.1.2
    rw [Submodule.mem_iInf] at h3
    have h4 := h3 L
    rw [Submodule.mem_iInf] at h4
    have h5 := h4 hL
    rwa [LinearMap.mem_ker, LinearMap.proj_apply] at h5
  funext i' L
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases hL : G.P.IsLatTup L
  · obtain ⟨⟨i0, L0⟩, hr0, hi0, γ, hγ⟩ := hR.2.2 i' L hL
    dsimp only at hi0 hγ
    subst hi0
    rw [Finset.sum_eq_single ⟨i0, L0⟩]
    · dsimp only
      rw [hγ, jdI_apply G i0 L0 γ _ (inv_of_mem G Hv F hF i0 L0), heqv]
    · rintro ⟨i1, L1⟩ hr1 hne
      apply Formalism.MainNotions.G.LatticeSystems.jd_zero
      by_cases h1 : i0 = i1
      · subst h1
        right
        rintro ⟨g, hg⟩
        refine hne (hR.2.1 ⟨i0, L0⟩ hr0 ⟨i0, L1⟩ hr1 rfl ⟨g⁻¹ * γ, ?_⟩).symm
        dsimp only
        rw [Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, ← hγ, hg, ← Formalism.MainNotions.G.LatticeSystems.jd_smul_mul, inv_mul_cancel,
          Formalism.MainNotions.G.LatticeSystems.jd_smul_one]
      · left
        exact fun h => h1 (by simpa using h)
    · intro h
      exact absurd hr0 h
  · rw [hzero i' L hL]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨i1, L1⟩ hr1
    apply Formalism.MainNotions.G.LatticeSystems.jd_zero
    right
    rintro ⟨g, rfl⟩
    exact hL (Formalism.MainNotions.G.LatticeSystems.jd_lat _ g L1 (hR.1 _ hr1))

theorem deltaI_rat (hA : RatActG G e) (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) (hξ : RatX G e ξ) :
    RatFn G e (delta G i L0 ξ) := by
  intro i' L
  classical
  unfold Formalism.MainNotions.G.LatticeSystems.delta
  split_ifs with h1 h2
  · exact hA i h1.choose ξ hξ
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem mRatSpan_inv (h2 : G.FinClasses) (hE : EquivSys G G.P.HtupW) (hA : RatActG G e) (hH : HRatInv G e) :
    MRatSpan G.P G.comp e G.M := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro F hF
    obtain ⟨reps, hR⟩ := jd_reps G h2
    rw [jdI_decomp G reps hR G.P.HtupW F hF]
    refine Submodule.sum_mem _ fun r hr => ?_
    have hlat : G.P.IsLatTup r.2 := hR.1 r hr
    have hval : F r.1 r.2 ∈ G.P.HtupW r.2 := ((jd_fmem G G.P.HtupW F).1 hF r.1).1 r.2 hlat
    have hsp : F r.1 r.2 ∈ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW r.2 ∧ InvAt G r.1 r.2 ξ ∧ RatX G e ξ} :=
      hH r.1 r.2 hlat ⟨hval, inv_of_mem G G.P.HtupW F hF r.1 r.2⟩
    generalize F r.1 r.2 = x at hsp
    induction hsp using Submodule.span_induction with
    | mem ξ hξ =>
      have hm : delta G r.1 r.2 ξ ∈ G.M := jdI_mem G G.P.HtupW hE r.1 r.2 hlat ξ hξ.1 hξ.2.1
      exact Submodule.subset_span
        ⟨⟨delta G r.1 r.2 ξ, Submodule.subset_span hm, deltaI_rat G e hA r.1 r.2 ξ hξ.2.2⟩, hm, rfl⟩
    | zero =>
      have : delta G r.1 r.2 (0 : G.P.Xsp) = 0 := by
        have := jd_smul G r.1 r.2 0 0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ h1' h2' => rw [jd_add]; exact Submodule.add_mem _ h1' h2'
    | smul a y _ h1' => rw [jd_smul]; exact Submodule.smul_mem _ _ h1'

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def tEL (D : D7) : D.what₂.Tau → D.host.E →+* D.what₂.LL :=
  fun τ => D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

theorem tEL_emb (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (tEL D τ x) = embT D τ x := by
  simp only [tEL, embT, Formalism.BasicNotions.Host.emb, RingHom.comp_apply]
  first
    | exact RingHom.congr_fun D.embE_φ₀ _
    | exact D.embE_φ₀ _
    | (rw [← D.embE_φ₀]; rfl)

def locAt (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) :
    LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w hg) where
  rk := (X.g u w hg).rk.trans (rank_eq_first_level D.R)
  pl := (X.g u w hg).pl
  eQ := fun v => (X.g u w hg).eQ v _ rfl
  spl := fun v => (X.g u w hg).spl _ ((X.g u w hg).pl v).2
  B := reGL (rank_eq_first_level D.R) _ B
  yG := fun i => reGL (rank_eq_first_level D.R) _ ((X.g u w hg).yG i).1
  gamI := fun i => (reGL (rank_eq_first_level D.R) D.host.E).toMonoidHom.comp
    ((UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0).subtype.comp ((X.g u w hg).gamI i))

def FrRat (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (X.g u w hg).fr w' h =
      bc (((RingHom.fst _ _).comp ((X.g u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

def StdB (D : D7) (B : GL (Fin D.R.k) D.host.E) : Prop :=
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rank_eq_first_level D.R) D.host.E B).1 * gramN D 0 (Nat.zero_le _) *
      (reGL (rank_eq_first_level D.R) D.host.E B).1 = 1 ∧
  ∀ x : Fin (D.R.N 0) → D.host.E, x ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔
    ∀ a, (((reGL (rank_eq_first_level D.R) D.host.E B)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 *ᵥ x) a ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range


set_option maxHeartbeats 1000000 in
structure CmpTied (D : D7) (X : Formalism.L2.Herm.Herm0 D) (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D)
    (c : LatCmp D) where

  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B

  fr_B : ∀ u w hg, FrRat X u w hg B
  tie : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    CmpTie ((T u).cls0).lev (embT D) D.what₂.embLL (tEL D) (D.gat u w hg) (c.embW u w hg)
      (locAt X u w hg B) (Gt.gat_pos u w hg)
      (fun x cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z))
      ((T u).cls0).y (c.cmp u w hg)

end Formalism.L2.G.Cmp

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.WeakApproxPI
section
open Formalism.MainNotions.G

theorem weakApprox_of_dvr (h : PI.WeakApproxDVR) {p : ℕ} (G : GAtP p) {E : Type} [Field E]
    (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)
    (hfr : ∀ v, IsFractionRing (G.P.W v) (G.P.Qq v))
    (hp : ∀ v, (p : G.P.Qq v) ≠ 0) (hpu : ∀ v, ¬ IsUnit (p : G.P.W v))
    (hden : ∀ v (x : G.P.Qq v) (N : ℕ), ∃ a : E, ∃ c : G.P.W v,
      iw v a = x + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c)
    (hdist : ∀ v v', v ≠ v' → ∃ a : E, iw v a ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      iw v' a ∉ Set.range (algebraMap (G.P.W v') (G.P.Qq v'))) :
    Formalism.L2.G.Cmp.WeakApprox G iw := by
  unfold PI.WeakApproxDVR at h
  unfold Formalism.L2.G.Cmp.WeakApprox
  have := hfr
  exact h E (Fin G.P.nV) G.P.W G.P.Qq iw p hp hpu hden hdist

theorem Formalism.L2.G.Cmp.weakApprox_of_approx_and_separation {p : ℕ} (G : GAtP p) {E : Type} [Field E]
    (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)
    (hfr : ∀ v, IsFractionRing (G.P.W v) (G.P.Qq v))
    (hp : ∀ v, (p : G.P.Qq v) ≠ 0) (hpu : ∀ v, ¬ IsUnit (p : G.P.W v))
    (hden : ∀ v (x : G.P.Qq v) (N : ℕ), ∃ a : E, ∃ c : G.P.W v,
      iw v a = x + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c)
    (hdist : ∀ v v', v ≠ v' → ∃ a : E, iw v a ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      iw v' a ∉ Set.range (algebraMap (G.P.W v') (G.P.Qq v'))) :
    Formalism.L2.G.Cmp.WeakApprox G iw :=
  weakApprox_of_dvr weak_approximation_dvr G iw hfr hp hpu hden hdist
end

