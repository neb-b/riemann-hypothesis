module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleTransportedWeilDatumDoubledTargetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelRule_transported_weilDatum_doubledTarget : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS : (AE D)ˣ →* Circle), IsHeckeChar D χS → ResEta D χS S.rank →
      ∀ (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
            (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
              fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ωd omp →
            GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JB)
              (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (GlobalTheory.WeilSchrodinger.transD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χS
              ((GlobalTheory.WeilM.diagCols (Fin T.rank) : Matrix (Fin T.rank ⊕ Fin T.rank) (Fin T.rank) (AE D)).submatrix
                finSumFinEquiv.symm id)
              (omp.comp (MonoidHom.inl _ _)) := by
  set_option maxHeartbeats 10000000 in
    exact @GlobalTheory.DblTargetSiegel.siegelRule_dblTarget
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.ThInt

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thetaInt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (h : M.Z ⟶ PSpace (cycAway n) N), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ h = spMap S.R.val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys M h hnorm hpt
  obtain ⟨e, hSym, hCrd⟩ := _root_.GlobalTheory.SiegTh.exists_symE_pCrd g n hg hn hno F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hCrd' : PCrd (M.pt ≫ h) e := by
    rw [hpt]; exact hCrd _ rfl
  have hDe : M.HasDiv e := _root_.GlobalTheory.UMin.hasDiv_of_pCrd_pt o Ω (cycAway n) M N h e hCrd'
  obtain ⟨-, -, -, hm, hm3, hmu, hNm, -, -⟩ := hTh
  obtain ⟨-, -, hSg, -, -⟩ := hSys
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : CharZero Ω := ArithBase.char o
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  letI := ρ.P.isAb.comm
  obtain ⟨j, hj1, hr⟩ := ρ.r_eq
  have hnodd := ρ.n_odd
  have hnp := ρ.n_prime
  have hrNodd : Odd (S.r * S.N) := by
    rw [hr, ρ.N_eq]; exact hnodd.pow.mul hnodd.pow.pow
  have hrN3 : 3 ≤ S.r * S.N := by
    have hn3 : 3 ≤ ρ.n := by
      have := hnp.two_le
      rcases hnodd with ⟨k, hk⟩
      omega
    have h1 : ρ.n ≤ S.r := by rw [hr]; exact Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ S.N := by have := S.N_ge; omega
    nlinarith
  refine _root_.GlobalTheory.ValCmp.hasDiv_of_forall_cDvr o Ω M S.Gam (Fin (N + 1)) S.th e (N + 1).factorial (Nat.factorial_pos _) hnorm hDe ?_
  intro V _ _ _ hV ξ emb hξ j₀ hj₀ hint
  haveI : IsDiscreteValuationRing V := ((GlobalTheory.LN.cDvr_iff V).1 hV).1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let val : S.R →+* Ω := S.R.val.toRingHom
  let i₀ : S.R →+* FractionRing V := emb.comp val
  let iK : S.R →+* K := io.comp i₀
  let i' : Ω →+* K := io.comp emb
  let σ : o →+* V := (Spec.preimage (ξ ≫ M.s)).hom
  have hmV : IsUnit (m : V) := by
    have h1 : IsUnit (m : o) := by rw [← map_natCast β]; exact hmu.map β
    rw [← map_natCast σ]; exact h1.map σ
  have hrNV : IsUnit ((S.r * S.N : ℕ) : V) := by rw [← map_natCast σ]; exact S.unit.map σ
  have hmK : (m : K) ≠ 0 := by
    have := hmV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  have hrNK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := hrNV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap i₀
  obtain ⟨P', φ, gp, hL'⟩ := GlobalTheory.UPoinc.exists_pol_baseChange ρ.P y
  letI := P'.isAb.comm
  have hS' : HypS P'.A P'.L :=
    _root_.GlobalTheory.SymBaseChange.hypS_baseChange _ _ ρ.P.A P'.A y φ ρ.P.L P'.L ρ.P.isLB P'.isLB gp hL' ρ.hypS
  have hPF0 : PolFib ρ.P.A ρ.P.L (8 * g) (𝟙 (Sp S.R)) :=
    ⟨ρ.P, 𝟙 _, by rw [ρ.g_eq, hSg], grpPullback_self _, GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB⟩
  have hPFK : PolFib ρ.P.A ρ.P.L (8 * g) (spMap iK ≫ 𝟙 (Sp S.R)) :=
    (_root_.GlobalTheory.UMin.FibMove.polFib_move (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) (8 * g) S.R (𝟙 _)).2 K iK hPF0
  let θK := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ iK
  obtain ⟨pt, c, hc⟩ := _root_.GlobalTheory.UMin.exists_thList (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) K
    (spMap iK ≫ 𝟙 (Sp S.R)) θK hm hmK hNm hPFK
  obtain ⟨pt', c', hc'⟩ := _root_.GlobalTheory.UMin.exists_thList (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) (S.r * S.N)
    ((S.r * S.N) ^ (4 * (8 * g))) K (spMap iK ≫ 𝟙 (Sp S.R)) θK hrNodd hrNK rfl hPFK
  have hgen := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o Ω S ρ K iK
  have hxy : spMap io ≫ y = spMap iK ≫ 𝟙 (Sp S.R) := by
    rw [Category.comp_id]; exact spMap_comp_ring i₀ io
  have h2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' := by
    rw [hxy]; exact ⟨θK, pt, pt', hgen, hc, hc'⟩
  obtain ⟨a, ha, hp1, hp2⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P' φ gp hL' hS' K io
    m (S.r * S.N) (N + 1) _ c c' hm hm3 hmV hrNodd hrN3 hrNV h2
  have hreal := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K iK _ pt' c' hc'
  have hlist : ∃ pt'' : Fin (N + 1) → (Over.mk (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R))) ⟶ ρ.P.A),
      ThList ρ.P.A ρ.P.L ρ.rig m (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R)))
        (SecAt.pull ρ.P.A ρ.P.L (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ val) i') pt'' c := by
    simp only [SecAt.pull]
    rw [pullS_comp ρ.P.A ρ.P.isLB]
    refine thList_congr ρ.th₁ ?_ (Over.homMk (spMap iK) rfl) _ ?_ hc
    · rw [Category.comp_id, Category.comp_id]; exact (spMap_comp_ring val i').symm
    · simp only [Over.comp_left, Over.homMk_left]; exact (spMap_comp_ring val i').symm
  obtain ⟨pt'', hpt''⟩ := hlist
  have hsym : ∀ j, io (emb (e j)) = symTup c j := fun j => by unfold SymE SymAt at hSym; exact hSym.2.2 K i' pt'' c hpt'' j
  have hj₀' : emb (e j₀) ≠ 0 := (map_ne_zero emb).2 hj₀
  have hint' : ∀ j, emb (e j) / emb (e j₀) ∈ Set.range (algebraMap V (FractionRing V)) := fun j => by
    rw [← map_div₀]; exact hint j
  obtain ⟨H1, b, hb, H2⟩ := _root_.GlobalTheory.UMin.prim_symTup_cmp V K io (N + 1) ((S.r * S.N) ^ (4 * (8 * g))) ((S.r * S.N) ^ 2) S.Gam c c' a
    (fun j => emb (e j)) (fun b => emb (S.th b)) ha (Nat.one_le_pow _ _ (by omega)) hp1 hp2 hsym hreal.1 hreal.2 j₀ hj₀'
    hint'
  refine ⟨fun b' => ?_, b, fun h0 => hb (by rw [h0, map_zero]), ?_⟩
  · rw [map_div₀, map_pow]; exact H1 b'
  · rw [map_div₀, map_pow]; exact H2

end GlobalTheory.SiegTh.ThInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralAnyBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.ThIntAll

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem relDim_eq_of_sharp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {P : PolAV F.X}
    (hPg : P.g = 8 * g) (hPs : GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X)) {T : Scheme.{0}} [Nonempty T] (Q : PolAV T)
    (u : T ⟶ F.X) (hQ : GlobalTheory.Poinc.SharpOver F W Q u) : Q.g = 8 * g := by
  obtain ⟨ψ, hψ, -⟩ := _root_.GlobalTheory.Poinc.sharpOver_unique g n F W Q P u (𝟙 F.X) u (Category.comp_id u) hQ hPs
  have h1 : SmoothOfRelativeDimension (8 * g) Q.A.hom := by
    rw [← hPg]; exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique Q.A.hom Q.smoothDim h1 ((η[Q.A]).left (Nonempty.some (inferInstanceAs (Nonempty T))))

theorem exists_symE_pCrd_of_sharp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {P : PolAV F.X}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {m N : ℕ} {f : F.X ⟶ PSpace (cycAway n) N} (hT : ThAt F W P rig m f)
    {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X) (hSg : S.g = 8 * g) (hρs : GlobalTheory.Poinc.SharpOver F W ρ.P u) :
    ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N),
      h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  obtain ⟨hPg, hPs, hrig, hm, -, hmu, hN, -, hf, -⟩ := hT
  haveI : CharZero Ω := hA.char
  have hSB : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  let v : S.R →+* Ω := S.R.val.toRingHom
  obtain ⟨P₀, φ, hg₀, hφ, hL₀⟩ := exists_isPolFibre polBaseChange_holds v ρ.P
  have hφ' : IsGrpPullback P₀.A ρ.P.A (spMap v ≫ 𝟙 (Sp S.R)) φ := by
    simpa using hφ
  have hL₀' : LBIso P₀.L (ρ.P.L.pull φ) := hL₀.symm
  have hfib : PolFib ρ.P.A ρ.P.L (8 * g) (spMap v ≫ 𝟙 (Sp S.R)) :=
    ⟨P₀, φ, by rw [hg₀, ρ.g_eq, hSg], hφ', hL₀'⟩
  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s =>
    (ρ.th₁_basis s).exists.elim fun r h => ⟨r 0, fun j => (h j).trans (Fin.sum_univ_one _)⟩
  let θ : SecAt ρ.P.A ρ.P.L (spMap v ≫ 𝟙 (Sp S.R)) := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap v ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.EmbPull.isGenSec_pullS ρ.P hSB _ hth
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UMin.SymRat.symAt_exists (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) Ω
    (spMap v ≫ 𝟙 (Sp S.R)) θ hm hN hfib
  have hmΩ : (m : Ω) ≠ 0 := by
    let κ : cycAway n →+* S.R := (Spec.preimage (u ≫ F.s)).hom
    have := (hmu.map κ).map v
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  refine ⟨e, ⟨by rw [hSg]; exact hN, hmΩ, he⟩, fun h hh => ?_⟩
  obtain ⟨ψ, hψ, hLψ⟩ := _root_.GlobalTheory.Poinc.sharpOver_unique g n F W ρ.P P u (𝟙 F.X) u (Category.comp_id u) hρs hPs
  have hα : IsGrpPullback P₀.A P.A ((spMap v ≫ u) ≫ 𝟙 F.X) (φ ≫ ψ) := by
    simpa using hφ.comp hψ
  have hLα : LBIso P₀.L (P.L.pull (φ ≫ ψ)) :=
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB φ) (pull_isLB P.isLB _) hL₀'
      (LBIso.trans (pull_isLB ρ.P.isLB φ) (pull_isLB (pull_isLB P.isLB ψ) φ) (pull_isLB P.isLB _)
        (RigidBundleGlue.LBIso.pull hLψ φ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp P.isLB ψ φ).symm)
  have key := _root_.GlobalTheory.UMin.pCrd_of_symAt F.X P.A P.L rig P.isLB hrig (8 * g) m N (cycAway n) F.X (𝟙 F.X) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig
    Ω (spMap v ≫ u) (spMap v ≫ 𝟙 (Sp S.R)) P₀ (φ ≫ ψ) φ θ e hm hN hf ρ.P.isLB ρ.rig_gen
    (by rw [hg₀, ρ.g_eq, hSg]) hα hLα hφ' hL₀' hθ he
  rw [hh, show algebraMap S.R Ω = v from RingHom.ext fun _ => rfl]
  simpa [Category.assoc] using key

theorem thetaInt_all : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → GlobalTheory.Poinc.ThetaInt F W f := by
  intro g n hg hn hno F W hW P rig m N f hTh o Ω _ _ _ _ S ρ u hρs _ M h hnorm hpt
  have hSg : S.g = 8 * g := by
    rw [← ρ.g_eq]; exact relDim_eq_of_sharp hTh.1 hTh.2.1 ρ.P u hρs
  obtain ⟨e, hSym, hCrd⟩ := exists_symE_pCrd_of_sharp hTh S ρ u hSg hρs
  have hCrd' : PCrd (M.pt ≫ h) e := by
    rw [hpt]; exact hCrd _ rfl
  have hDe : M.HasDiv e := _root_.GlobalTheory.UMin.hasDiv_of_pCrd_pt o Ω (cycAway n) M N h e hCrd'
  obtain ⟨-, -, -, hm, hm3, hmu, hNm, -, -⟩ := hTh
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : CharZero Ω := ArithBase.char o
  haveI : NeZero (S.r * S.N) := ⟨by have := S.r_pos; have := S.N_ge; positivity⟩
  letI := ρ.P.isAb.comm
  obtain ⟨j, hj1, hr⟩ := ρ.r_eq
  have hnodd := ρ.n_odd
  have hnp := ρ.n_prime
  have hrNodd : Odd (S.r * S.N) := by
    rw [hr, ρ.N_eq]; exact hnodd.pow.mul hnodd.pow.pow
  have hrN3 : 3 ≤ S.r * S.N := by
    have hn3 : 3 ≤ ρ.n := by
      have := hnp.two_le
      rcases hnodd with ⟨k, hk⟩
      omega
    have h1 : ρ.n ≤ S.r := by rw [hr]; exact Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ S.N := by have := S.N_ge; omega
    nlinarith
  refine _root_.GlobalTheory.ValCmp.hasDiv_of_forall_cDvr o Ω M S.Gam (Fin (N + 1)) S.th e (N + 1).factorial (Nat.factorial_pos _)
    ((GlobalTheory.isNormalScheme_iff_pred _).1 hnorm) hDe ?_
  intro V _ _ _ hV ξ emb hξ j₀ hj₀ hint
  haveI : IsDiscreteValuationRing V := ((GlobalTheory.LN.cDvr_iff V).1 hV).1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let val : S.R →+* Ω := S.R.val.toRingHom
  let i₀ : S.R →+* FractionRing V := emb.comp val
  let iK : S.R →+* K := io.comp i₀
  let i' : Ω →+* K := io.comp emb
  let σ : o →+* V := (Spec.preimage (ξ ≫ M.s)).hom
  let τ : cycAway n →+* V := (Spec.preimage (ξ ≫ h ≫ PSpace.str (cycAway n) N)).hom
  have hmV : IsUnit (m : V) := by
    rw [← map_natCast τ]; exact hmu.map τ
  have hrNV : IsUnit ((S.r * S.N : ℕ) : V) := by rw [← map_natCast σ]; exact S.unit.map σ
  have hmK : (m : K) ≠ 0 := by
    have := hmV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  have hrNK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := hrNV.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap i₀
  obtain ⟨P', φ, gp, hL'⟩ := GlobalTheory.UPoinc.exists_pol_baseChange ρ.P y
  letI := P'.isAb.comm
  have hS' : HypS P'.A P'.L :=
    _root_.GlobalTheory.SymBaseChange.hypS_baseChange _ _ ρ.P.A P'.A y φ ρ.P.L P'.L ρ.P.isLB P'.isLB gp hL' ρ.hypS
  have hPF0 : PolFib ρ.P.A ρ.P.L (8 * g) (𝟙 (Sp S.R)) :=
    ⟨ρ.P, 𝟙 _, by rw [ρ.g_eq, hSg], grpPullback_self _, GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB⟩
  have hPFK : PolFib ρ.P.A ρ.P.L (8 * g) (spMap iK ≫ 𝟙 (Sp S.R)) :=
    (_root_.GlobalTheory.UMin.FibMove.polFib_move (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) (8 * g) S.R (𝟙 _)).2 K iK hPF0
  let θK := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ iK
  obtain ⟨pt, c, hc⟩ := _root_.GlobalTheory.UMin.exists_thList (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) K
    (spMap iK ≫ 𝟙 (Sp S.R)) θK hm hmK hNm hPFK
  obtain ⟨pt', c', hc'⟩ := _root_.GlobalTheory.UMin.exists_thList (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) (S.r * S.N)
    ((S.r * S.N) ^ (4 * (8 * g))) K (spMap iK ≫ 𝟙 (Sp S.R)) θK hrNodd hrNK rfl hPFK
  have hgen := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o Ω S ρ K iK
  have hxy : spMap io ≫ y = spMap iK ≫ 𝟙 (Sp S.R) := by
    rw [Category.comp_id]; exact spMap_comp_ring i₀ io
  have h2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' := by
    rw [hxy]; exact ⟨θK, pt, pt', hgen, hc, hc'⟩
  obtain ⟨a, ha, hp1, hp2⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P' φ gp hL' hS' K io
    m (S.r * S.N) (N + 1) _ c c' hm hm3 hmV hrNodd hrN3 hrNV h2
  have hreal := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K iK _ pt' c' hc'
  have hlist : ∃ pt'' : Fin (N + 1) → (Over.mk (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R))) ⟶ ρ.P.A),
      ThList ρ.P.A ρ.P.L ρ.rig m (spMap i' ≫ (spMap val ≫ 𝟙 (Sp S.R)))
        (SecAt.pull ρ.P.A ρ.P.L (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ val) i') pt'' c := by
    simp only [SecAt.pull]
    rw [pullS_comp ρ.P.A ρ.P.isLB]
    refine thList_congr ρ.th₁ ?_ (Over.homMk (spMap iK) rfl) _ ?_ hc
    · rw [Category.comp_id, Category.comp_id]; exact (spMap_comp_ring val i').symm
    · simp only [Over.comp_left, Over.homMk_left]; exact (spMap_comp_ring val i').symm
  obtain ⟨pt'', hpt''⟩ := hlist
  have hsym : ∀ j, io (emb (e j)) = symTup c j := fun j => by unfold SymE SymAt at hSym; exact hSym.2.2 K i' pt'' c hpt'' j
  have hj₀' : emb (e j₀) ≠ 0 := (map_ne_zero emb).2 hj₀
  have hint' : ∀ j, emb (e j) / emb (e j₀) ∈ Set.range (algebraMap V (FractionRing V)) := fun j => by
    rw [← map_div₀]; exact hint j
  obtain ⟨H1, b, hb, H2⟩ := _root_.GlobalTheory.UMin.prim_symTup_cmp V K io (N + 1) ((S.r * S.N) ^ (4 * (8 * g))) ((S.r * S.N) ^ 2) S.Gam c c' a
    (fun j => emb (e j)) (fun b => emb (S.th b)) ha (Nat.one_le_pow _ _ (by omega)) hp1 hp2 hsym hreal.1 hreal.2 j₀ hj₀'
    hint'
  refine ⟨fun b' => ?_, b, fun h0 => hb (by rw [h0, map_zero]), ?_⟩
  · rw [map_div₀, map_pow]; exact H1 b'
  · rw [map_div₀, map_pow]; exact H2

end GlobalTheory.SiegTh.ThIntAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField

namespace GlobalTheory.BigTop.Fun.ThbTie

theorem sqRank_half {D : D7} (ij : Sq D) : sqRank D ij / 2 = GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
  congr 1
  ring

theorem htLe_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] {g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ} {z : K} {B : ℝ}
    (h : Formalism.PairingDivisionLocalBalance.HtLe g z B) : 0 ≤ B :=
  (finsum_nonneg fun w => mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (abs_nonneg _)).trans h.2

theorem htLe_one_zero {K : Type} [Field K] [NumberField K] [StarRing K] {B : ℝ} (hB : 0 ≤ B) :
    Formalism.PairingDivisionLocalBalance.HtLe (fun _ => (0 : ℤ)) (1 : K) B := by
  have e : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => Formalism.DivisionValues.lw w * |((Formalism.DivisionValues.vw w (1 : K) + 0 : ℤ) : ℝ)|) = fun _ => 0 := by
    funext w
    simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  refine ⟨?_, ?_⟩
  · rw [e]
    simp
  · rw [e, finsum_zero]
    exact hB

end GlobalTheory.BigTop.Fun.ThbTie


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialStrictHenselisationOriginStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_trivial_strict_henselisation_origin : GlobalTheory.LocAcyc.KeyOrigin := by
  first | (exact @GlobalTheory.KeyOriginCut.keyOrigin) | (exact GlobalTheory.KeyOriginCut.keyOrigin) | (intros; apply GlobalTheory.KeyOriginCut.keyOrigin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_trait_uniformisations_matching_data : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (D₁ : DegData V (maximalIdeal V)) (A₁ : PolAV (Sp (FractionRing V))) (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (D₂ : DegData V (maximalIdeal V)) (A₂ : PolAV (Sp (FractionRing V))) (G₂ : Over (Sp V)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing V) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ ∀ k : ℕ, 1 ≤ k → ∀ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) k) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) k) (x₁ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₁.A) (x₂ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A₂.A), QkToAkU U₁.toUnifPre (AlgebraicClosure (FractionRing V)) k p₁ x₁ → QkToAkU U₂.toUnifPre (AlgebraicClosure (FractionRing V)) k p₂ x₂ → x₁.left ≫ α₁ = x₂.left ≫ α₂ → QImg b φ p₁ p₂ := by
  first | exact @GlobalTheory.TInj.two_unif_match | exact GlobalTheory.TInj.two_unif_match | (intros; apply GlobalTheory.TInj.two_unif_match <;> assumption)
end

