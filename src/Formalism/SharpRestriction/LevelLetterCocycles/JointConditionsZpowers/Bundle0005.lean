module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem archimedean_signature_matching_of_liftingTheory (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA : ℝ) (CB : ℝ) (CK : ℝ) (C : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching D HW F CA CB CK := by
  unfold Formalism.MainNotions.ElementDenominator.ArchimedeanSignatureMatching
  exact lift_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_five_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm5 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm5
  exact wach_of_lifting_package D HW F C CA CB CK h54

theorem lifting_input_six_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ)
    (h54 : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.ElementDenominator.adm6 D HW F := by
  unfold Formalism.MainNotions.ElementDenominator.adm6
  exact lifting_local_of_package D HW F C CA CB CK h54

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module

def CrysOnCond (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) Y.ρ →
    Formalism.MainNotions.LocalSituation.IsCrysOn (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h)
      (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h).W.GKs Y

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal

open NumberField IsDedekindDomain

theorem galois_condition_six_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : Formalism.MainNotions.SumRepresentations.ConclusionG6 D) (hg : Formalism.MainNotions.N.HG D.nd D.naut i) (hr : Formalism.MainNotions.N.GoodR D.nd i r) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG6 (D := D) i r := by
  intro x hx
  exact (D.Z_tie i x).2 (h32 i hg r hr x hx).1

theorem galois_condition_five_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (h32 : Formalism.MainNotions.SumRepresentations.ConclusionG5 D) (hg : Formalism.MainNotions.N.HG D.nd D.naut i) (hr : Formalism.MainNotions.N.GoodR D.nd i r) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG5 (D := D) i r := by
  intro w hw
  obtain ⟨ha, hb, -⟩ := h32 i hg r hr w hw (D.nd.SQ_l i w hw)
  exact ⟨ha, fun hk hS _ => hb hk hS⟩

def LitGoodO : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL)

theorem bloch_kato_annihilators_of (D : D7) (i : D.nd.Loc) (h55 : Formalism.MainNotions.LocalSituation.Conclusion5 D) (hT : Formalism.MainNotions.LocalSituation.adm3 D)
    (hDim : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm8 D) (hO : LitGoodO) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admBK (D := D) i := by
  intro w hw C
  exact ⟨Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _ (hT _ _) (hO _ _), hDim _ _ _,
    fun _ => Formalism.MainNotions.TruncatedSeriesCountingIdentities.bkBAt_of_core _ _ _ (h55 _ _).2.2.2.1 (hO _ _)⟩

theorem integers_t2Space (D : D7) (i : D.nd.Loc) : T2Space (D.nd.O i) := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  have hH : IsHausdorff (IsLocalRing.maximalIdeal (D.nd.O i)) (D.nd.O i) :=
    (D.nd.O_complete i).toIsHausdorff
  by_contra hcon
  push Not at hcon
  apply hx
  apply hH.haus' x
  intro n
  have hU : ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal _) : Set (D.nd.O i)) ∈ nhds 0 :=
    ((isAdic_iff.mp (D.nd.O_adic i)).1 n).mem_nhds (Ideal.zero_mem _)
  have := hcon _ hU
  rw [SModEq.zero]
  simpa using this

theorem cycZ_one_of_Ine (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hv : v ∉ placesOver D.host.E (D.nd.l i)) (g : GE D.nd)
    (hg : g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq (v := v) hv (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hg.2 x hx) n]
  simp

theorem inertia_character_mem_zpowers (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E))
    (hgen : TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v))
    (htame : ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), D.nd.chi i 1 σ = 1)
    (hfin : IsOfFinOrder (D.nd.chi i 1 (D.nd.gam0 i v))) (g : GE D.nd)
    (hg : g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    D.nd.chi i 1 g ∈ Subgroup.zpowers (D.nd.chi i 1 (D.nd.gam0 i v)) := by
  have := integers_t2Space D i
  set ζ := D.nd.chi i 1 (D.nd.gam0 i v) with hζ
  have hS : ((Subgroup.zpowers ζ : Subgroup (D.nd.O i)ˣ) : Set (D.nd.O i)ˣ).Finite :=
    finite_zpowers.mpr hfin
  have hcl : IsClosed (((Subgroup.zpowers ζ).comap (D.nd.chi i 1) : Subgroup (GE D.nd)) : Set (GE D.nd)) := by
    have e : (((Subgroup.zpowers ζ).comap (D.nd.chi i 1) : Subgroup (GE D.nd)) : Set (GE D.nd)) =
        ⋃ u ∈ ((Subgroup.zpowers ζ : Subgroup (D.nd.O i)ˣ) : Set (D.nd.O i)ˣ),
          {g | ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) = (u : D.nd.O i)} := by
      ext g
      simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Set.mem_iUnion,
        Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro h
        exact ⟨_, h, rfl⟩
      · rintro ⟨u, hu, h⟩
        rwa [Units.ext h]
    rw [e]
    exact hS.isClosed_biUnion fun u _ => isClosed_eq (D.nd.chi_cont i 1) continuous_const
  have hle : Subgroup.closure (insert (D.nd.gam0 i v) (wildSet D.nd (D.nd.plOm.1 v))) ≤
      (Subgroup.zpowers ζ).comap (D.nd.chi i 1) := by
    rw [Subgroup.closure_le]
    intro σ hσ
    rcases hσ with rfl | hσ
    · exact Subgroup.mem_zpowers ζ
    · show D.nd.chi i 1 σ ∈ Subgroup.zpowers ζ
      rw [htame σ hσ]
      exact Subgroup.one_mem _
  exact closure_minimal hle hcl (hgen hg)

def TameCharacterConditions (D : D7) (i : D.nd.Loc) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 D.host.E),
    (v ∈ D.nd.Q i ∨ (v ∈ D.nd.S i ∧ (v ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')))) →
    ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 v), D.nd.chi i 1 σ = 1) ∧
  Formalism.MainNotions.SumRepresentations.At.Del D.nd i

theorem galois_condition_five_extra_of (D : D7) (i : D.nd.Loc) (hc : TameCharacterConditions D i) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  intro v hv
  have hgen : TameGen D.nd (D.nd.plOm.1 v) (D.nd.gam0 i v) := (D.nd.restN_tameGenerator_generates i v hv).2
  have hl := D.nd.SQ_l i v hv
  refine ⟨hgen, ?_, ?_, ?_⟩
  · intro c hc' g hg
    rw [Finset.mem_Icc] at hc'
    rw [D.nd.chi_def i c hc'.1 hc'.2]
    simp [cycZ_one_of_Ine D i v hl g hg]
  · intro hQ hz
    obtain ⟨g, hg, hne⟩ := D.nd.chi_ram_Q i v hQ
    have h1 : D.nd.chi i 1 (D.nd.gam0 i v) = 1 := Units.ext hz
    have := inertia_character_mem_zpowers D i v hgen (hc.1 v (Or.inl hQ)) (by rw [h1]; exact IsOfFinOrder.one) g hg
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    exact hne this
  · intro hS hp
    have hov : v ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) := by
      rcases hp with hp | ⟨h1, hp⟩
      · have : D.nd.l i ≠ D.host.pde := fun h => hl (h ▸ hp)
        rwa [if_neg this]
      · rwa [if_pos h1]
    have hcard := hc.2 v hS hov
    set ζ := D.nd.chi i 1 (D.nd.gam0 i v) with hζ
    have hmem : ζ ∈ (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1) :=
      ⟨_, D.nd.locNd_chebotarevPlace_mem i v, rfl⟩
    have : Finite ↥((Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have hfin : IsOfFinOrder ζ := by
      have := isOfFinOrder_of_finite (⟨ζ, hmem⟩ : ↥((Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1)))
      exact (Subgroup.subtype _).isOfFinOrder this
    have heq : (Ine (F := D.host.E) (D.nd.plOm.1 v)).map (D.nd.chi i 1) = Subgroup.zpowers ζ := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        exact inertia_character_mem_zpowers D i v hgen (hc.1 v (Or.inr ⟨hS, hp⟩)) hfin g hg
      · rw [Subgroup.zpowers_le]
        exact hmem
    have hord : orderOf ζ = 15 := by
      rw [← Nat.card_zpowers, ← heq, hcard]
    have hprim : IsPrimitiveRoot ((ζ : (D.nd.O i)ˣ) : D.nd.O i) 15 := by
      rw [IsPrimitiveRoot.coe_units_iff, ← hord]
      exact IsPrimitiveRoot.orderOf ζ
    have hroot : (Polynomial.cyclotomic 15 (D.nd.O i)).eval ((ζ : (D.nd.O i)ˣ) : D.nd.O i) = 0 :=
      hprim.isRoot_cyclotomic (by norm_num)
    have h1 : (Polynomial.cyclotomic 15 (D.nd.O i)).eval 1 = 1 := by
      apply Polynomial.eval_one_cyclotomic_not_prime_pow
      intro p hp k hk
      have h3 : 3 ∣ p ^ k := by rw [hk]; norm_num
      have h5 : 5 ∣ p ^ k := by rw [hk]; norm_num
      have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
      have e5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (Nat.prime_five.dvd_of_dvd_pow h5)
      omega
    have hd := Polynomial.sub_dvd_eval_sub ((ζ : (D.nd.O i)ˣ) : D.nd.O i) 1 (Polynomial.cyclotomic 15 (D.nd.O i))
    rw [hroot, h1, zero_sub] at hd
    exact isUnit_of_dvd_unit hd (isUnit_one.neg)

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.HerrDescriptionH1OfHerr
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem herr_description_H1_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.DeltaInvariantLattices.adm2 D HW F := by
  intro l _ K s LL hg T _ _
  refine ⟨(h l K s LL hg).2.1 T, fun _ hp => ?_⟩
  have hA := (h l K s LL hg).1 (fun e => absurd e hp) T
  exact ⟨hA.1, fun w => hA.2.1 w⟩

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module

section Ker

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [TopologicalSpace LL] [IsTopologicalRing LL] [CommRing O] [Algebra O LL]

def LocLat.ofGRep (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ) : LocLat G Qp LL O :=
  { V := A.V, ρ := A.ρ, cont := A.cont, L := L }

variable (Yt : LocLat G Qp LL O) (p : Yt.V →ₗ[LL] LL) (e₀ : Yt.V) (hpe : p e₀ = 1)

theorem ker_stable (hp : ∀ g v, p (Yt.ρ g v) = p v) :
    ∀ g, ∀ u ∈ LinearMap.ker p, Yt.ρ g u ∈ LinearMap.ker p := by
  intro g u hu
  rw [LinearMap.mem_ker] at hu ⊢
  exact (hp g u).trans hu

def kerProj : Yt.V →ₗ[LL] ↥(LinearMap.ker p) :=
  LinearMap.codRestrict _ (LinearMap.id - (LinearMap.toSpanSingleton LL Yt.V e₀) ∘ₗ p) (by
    intro v
    rw [LinearMap.mem_ker]
    simp [hpe])

theorem kerProj_coe (v : Yt.V) : ((kerProj Yt p e₀ hpe v : ↥(LinearMap.ker p)) : Yt.V) = v - p v • e₀ := rfl

theorem kerProj_of_mem (u : ↥(LinearMap.ker p)) : kerProj Yt p e₀ hpe (u : Yt.V) = u := by
  apply Subtype.ext
  rw [kerProj_coe, LinearMap.mem_ker.mp u.2, zero_smul, sub_zero]

def kerT : Submodule O ↥(LinearMap.ker p) :=
  Yt.L.T.comap ((LinearMap.ker p).subtype.restrictScalars O)

theorem kerT_eq_map (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) :
    kerT Yt p = Yt.L.T.map ((kerProj Yt p e₀ hpe).restrictScalars O) := by
  ext u
  constructor
  · intro hu
    exact ⟨(u : Yt.V), hu, kerProj_of_mem Yt p e₀ hpe u⟩
  · rintro ⟨v, hv, rfl⟩
    show ((kerProj Yt p e₀ hpe v : ↥(LinearMap.ker p)) : Yt.V) ∈ Yt.L.T
    rw [kerProj_coe]
    obtain ⟨a, ha⟩ := hint v hv
    rw [← ha, algebraMap_smul]
    exact Yt.L.T.sub_mem hv (Yt.L.T.smul_mem a he₀)

theorem kerT_free [IsDomain O] [IsPrincipalIdealRing O] : Module.Free O ↥(kerT Yt p) := by
  have := Yt.L.free
  have : Module.Finite O ↥Yt.L.T := Module.Finite.iff_fg.mpr Yt.L.fg
  let N' : Submodule O ↥Yt.L.T := LinearMap.ker ((p.restrictScalars O) ∘ₗ Yt.L.T.subtype)
  obtain ⟨n, ⟨b⟩⟩ := Submodule.nonempty_basis_of_pid (Module.Free.chooseBasis O ↥Yt.L.T) N'
  have hN : Module.Free O ↥N' := Module.Free.of_basis b
  let eqv : ↥N' ≃ₗ[O] ↥(kerT Yt p) :=
    { toFun := fun t => ⟨⟨(t : ↥Yt.L.T), t.2⟩, (t : ↥Yt.L.T).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun u => ⟨⟨((u : ↥(LinearMap.ker p)) : Yt.V), u.2⟩, (u : ↥(LinearMap.ker p)).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Free.of_equiv eqv

include hpe in
theorem kerT_span (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) :
    Submodule.span LL ((kerT Yt p : Submodule O ↥(LinearMap.ker p)) : Set ↥(LinearMap.ker p)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have h1 : (u : Yt.V) ∈ Submodule.span LL (Yt.L.T : Set Yt.V) := by
    rw [Yt.L.span]
    trivial
  have h2 := Submodule.mem_map_of_mem (f := kerProj Yt p e₀ hpe) h1
  rw [kerProj_of_mem, Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, kerT_eq_map Yt p e₀ hpe hint he₀]
  exact ⟨v, hv, rfl⟩

def kerLat [IsDomain O] [IsPrincipalIdealRing O] (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) :
    Lattice (O := O) (subRho (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp)) where
  T := kerT Yt p
  stable := fun g x hx => Yt.L.stable g x hx
  fg := by
    rw [kerT_eq_map Yt p e₀ hpe hint he₀]
    exact Yt.L.fg.map _
  free := kerT_free Yt p
  span := kerT_span Yt p e₀ hpe hint he₀

def kerY [IsDomain O] [IsPrincipalIdealRing O] (hp : ∀ g v, p (Yt.ρ g v) = p v)
    (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap O LL)) (he₀ : e₀ ∈ Yt.L.T) : LocLat G Qp LL O :=
  LocLat.ofGRep ((GRep.ofLat Yt).sub (LinearMap.ker p) (ker_stable Yt p hp)) (kerLat Yt p e₀ hpe hp hint he₀)


variable (G Qp LL O) in
def trivZ (hinj : Function.Injective (algebraMap O LL)) : LocLat G Qp LL O :=
  { V := LL
    ρ := 1
    cont := fun _ => continuous_const
    L :=
      { T := LinearMap.range (Algebra.linearMap O LL)
        stable := fun _ _ hx => hx
        fg := by
          rw [LinearMap.range_eq_map]
          exact Submodule.FG.map _ Module.Finite.fg_top
        free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
        span := by
          rw [eq_top_iff]
          intro x _
          have h1 : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
            Submodule.subset_span ⟨1, by simp⟩
          have := Submodule.smul_mem _ x h1
          simpa using this } }

end Ker

def JointConditionTameBound (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (π : D.nd.X i) (M0 h0 cB : ℕ) : Prop :=
  D.nd.l i ≠ 2 ∧ ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.inert D.nbr i w hw = IK (D.nbr i w hw).Kw ∧ (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 ∧
    ∀ (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hs : Good (D.nbr i w hw).Kw 1 C.LL)
      (Y : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)),
      IsCrys (Br.PD D.loc D.nbr i w hw) Y.ρ →
      (∀ τ, JumpsInV (Br.PD D.loc D.nbr i w hw) Y.ρ τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}) →
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y,
        -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      ∀ e < D.R.t, Formalism.MainNotions.LocalSituation.cTBY
        (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y M0 h0 e ≤ cB

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

theorem locC_rTwO (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x) =
      twistM (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem locC_cont (D : D7) (i : D.nd.Loc) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (v : Fin k → ↥C.LL.1) :
    Continuous fun g => (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g).mulVec v := by
  have hmat : Continuous fun g => Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C M g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
        ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
      Continuous.subtype_mk continuous_subtype_val _
    exact h3.comp (h2.comp h1)
  exact hmat.matrix_mulVec continuous_const

theorem rTwO_cont (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x : D.nd.X i) : Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul (hr x)

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LocalInputFourteenOfLocal
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem class_map_naturality_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.LiftingTheory.adm21 D HW F := by
  intro l _ K s LL hg
  obtain ⟨hA, -, hN⟩ := h l K s LL hg
  refine ⟨hN, fun _ hl => ?_⟩
  intro T T' f pr pr' hpr
  have h2 : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg) = 2 →
      ∃ i : (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg).K, i ^ 2 = -1 := by
    intro h2
    exact absurd (((D.loc l).PD_p K).symm.trans h2) hl
  exact ((hA h2 T).2.2 T' f pr pr' hpr).symm

end Formalism.MainNotions.N
end
end

