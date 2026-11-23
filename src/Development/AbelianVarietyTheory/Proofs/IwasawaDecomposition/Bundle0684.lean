module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpectedShapeLevelIntegralAndUnipotentAtTypePlac
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevShapeBound

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_of_compAt (s : SplitPlace L) {x y : AL L}
    (h : compAt L s.v x = compAt L s.v y) : s.proj x = s.proj y := by
  have key : ∀ z : AL L, s.proj z =
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ (s.v.adicCompletion (maximalRealSubfield L)))
        (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
  rw [key, key, h]

theorem loc_eq_of_comp (s : SplitPlace L) {x y : GAf L n}
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)) :
    s.loc n x = s.loc n y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  exact proj_eq_of_compAt s hij

end Gen

theorem bound : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  intro D η J hG hS κ hκ
  obtain ⟨hprod, hpara, huni, hhyp⟩ := hS

  have hloc : ∀ w, ∃ κ' ∈ J, κ' ∈ Umax D.host.E D.R.nV ∧
      (κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) =
        (κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) := by
    intro w
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ w
    refine ⟨κ', hκ', ?_, heq⟩
    by_cases hg : w ∈ gPl D
    · obtain ⟨k, v, s, hsv, hsw⟩ := hG.2.1 w hg
      subst hsv
      have hu := (huni k v s hsw κ' htr).1 hκ'
      exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hu.1.1
    · by_cases hq : w ∈ qPl D η
      · obtain ⟨s, hsv, hs⟩ := hpara w hq
        subst hsv
        have hp := (hs κ' htr).1 hκ'
        exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hp.1
      · refine (hhyp κ' ?_).1 hκ'
        intro u hu
        apply htr u
        rintro rfl
        simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hu
        rcases hu with h | h
        · exact hg h
        · exact hq h
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.FormInner.mem_ALint_of_comp
    intro w
    obtain ⟨κ', -, hU, heq⟩ := hloc w
    refine ⟨(κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)) i j, hU i j, ?_⟩
    have := congrFun (congrFun heq i) j
    simpa only [Matrix.map_apply] using this
  · intro k v s hsw
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ s.v
    have hu := (huni k v s hsw κ' htr).1 hκ'
    rwa [loc_eq_of_comp s heq] at hu

end GlobalTheory.LevShapeBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundle
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

open GlobalTheory.Mem.R3 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links



set_option maxHeartbeats 4000000 in
theorem side_mk_eq_upd {D : D7} {nch : NChoice D} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {J : Formalism.L2.Pj.CoreJ D} [Algebra J.Q.c.F D.what₂.LL] (R : RealDat3 D A3 J.Q.c.F)
    (kap : ℝ) (lam : type_of% R.lam3) (err : type_of% R.err0) (P0 P0' : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (ψ0' : P0' →* D.what₂.LLˣ)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (v v' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
    (S S' : Formalism.IndefR.NX.RatDat D.ntw) (Y : Formalism.IndefR.NX.NExpRealS ((R.updS kap lam).withErr err) cG S)
    (Y' : Formalism.IndefR.NX.NExpRealS R cG S') (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D R.C nch)
    (tp' : Formalism.L2.Host.TupTied D cf nch) (hP : P0 = P0') (hψ : HEq ψ0 ψ0') (hv : HEq v v') (hS : HEq S S') (hfi : HEq Y.fi Y'.fi)
    (heF : HEq Y.eF Y'.eF) (hcf : R.C = cf) (htp : HEq tp tp') :
    ({ G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := (R.updS kap lam).withErr err, P0 := P0, ψ0 := ψ0, cG := cG, v₀ := v, S := S, YS := Y, cf := R.C, tp := tp } : Side D nch) =
      Side.upd { G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := R, P0 := P0', ψ0 := ψ0', cG := cG, v₀ := v', S := S', YS := Y', cf := cf, tp := tp' } kap lam err := by
  subst hP hcf
  cases eq_of_heq hψ
  cases eq_of_heq hv
  cases eq_of_heq hS
  cases eq_of_heq htp
  obtain ⟨fi, _, _, _, eF, _, _⟩ := Y
  obtain ⟨fi', _, _, _, eF', _, _⟩ := Y'
  replace hfi : fi = fi' := (eq_of_heq hfi)
  replace heF : eF = eF' := (eq_of_heq heF)
  subst hfi heF
  rfl


set_option maxHeartbeats 4000000 in
theorem side_eq_upd {D : D7} {O : Obj D} (x : R3.TwIn O.ex) (s : Side D O.ex.nch) (kap : ℝ) (lam : type_of% s.R.lam3)
    (err : type_of% s.R.err0) (F : Face3 D s.A3) (Sx : Formalism.IndefR.NX.RatDat D.ntw) (YS : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx)
    (Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch)
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨s.G, s.grp, s.fin, s.Pl0, s.I0, s.T, s.A3, s.J, s.alg, (s.R.updS kap lam).withErr err, F, s.cG⟩)
    (hP : F.P0 = s.P0) (hψ : HEq F.ψ0 s.ψ0) (hv : HEq x.geo.v₀ s.v₀) (hS : HEq Sx s.S) (hfi : HEq YS.fi s.YS.fi)
    (heF : HEq YS.eF s.YS.eF) (hcf : s.R.C = s.cf) (htp : HEq Tp s.tp) :
    ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := Sx, YS := YS, cf := x.R.C, tp := Tp } : Side D O.ex.nch) = s.upd kap lam err := by
  obtain ⟨G, Pl0, I0, T, A3, J, R, P0, ψ0, cG, v₀, S, Y, cf, tp⟩ := s
  obtain ⟨G', Pl0', I0', T', A3', core, R', F', cG', geo⟩ := x
  cases pack
  exact side_mk_eq_upd R kap lam err _ _ _ _ cG _ _ _ _ _ _ _ _ _ hP hψ hv hS hfi heF hcf htp


end GlobalTheory.PlugPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexification
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

theorem exists_finset_eval_eq_zero {X K W : Type} [Field K] [AddCommGroup W] [Module K W]
    (V : Submodule K (X → W)) [FiniteDimensional K V] :
    ∃ P : Finset X, ∀ f ∈ V, (∀ x ∈ P, f x = 0) → f = 0 := by
  classical
  let N : Finset X → Submodule K V := fun P =>
    ⨅ x ∈ P, LinearMap.ker ((LinearMap.proj (R := K) (φ := fun _ : X => W) x).comp V.subtype)
  have hN : ∀ P (f : V), f ∈ N P ↔ ∀ x ∈ P, (f : X → W) x = 0 := by
    intro P f; simp [N, Submodule.mem_iInf]
  obtain ⟨_, ⟨P, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min (Set.range N) ⟨_, ⟨∅, rfl⟩⟩
  refine ⟨P, fun f hf h0 => ?_⟩
  have key : ∀ x, N P ≤ N (insert x P) := by
    intro x
    have hle : N (insert x P) ≤ N P := fun g hg =>
      (hN _ _).2 fun y hy => (hN _ _).1 hg y (Finset.mem_insert_of_mem hy)
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle fun h => hne h.ge)
  funext x
  exact (hN _ _).1 (key x ((hN P ⟨f, hf⟩).2 h0)) x (Finset.mem_insert_self x P)

section Omega
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W']
  [Fintype ι] [DecidableEq ι]

def coordCx (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') : W →ₛₗ[e] W' where
  toFun w := b'.equivFun.symm fun i => e (b.equivFun w i)
  map_add' x y := b'.equivFun.injective (by
    simp only [map_add (f := _), LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.add_apply, map_add (f := _)])
  map_smul' a x := b'.equivFun.injective (by
    simp only [map_smul, LinearEquiv.apply_symm_apply]; funext i; simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply])

theorem coordCx_coord (e : K →+* ℂ) (b : Module.Basis ι K W) (b' : Module.Basis ι ℂ W') (w : W) (i : ι) :
    b'.equivFun (coordCx e b b' w) i = e (b.equivFun w i) := by
  simp only [coordCx, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]

end Omega

theorem finrank_typeSp_cx : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (e : K →+* ℂ) (W W' : Type) [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation K (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W') (J : Subgroup (GAf L n)) (χ : J →* Kˣ), WtMatch e ρ ρ' → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → FiniteDimensional K (NX.TypeSpF L n K ρ J χ) → Module.finrank ℂ (NG.TypeSp ρ' J (cx e χ)) = Module.finrank K (NX.TypeSpF L n K ρ J χ) := by
  intro L _ _ _ n K _ e W W' _ _ _ _ ρ ρ' J χ hW hN hfin
  classical
  obtain ⟨ι, _, _, b, b', hM⟩ := hW
  letI : Algebra K ℂ := e.toAlgebra
  let β := Module.Basis.ofVectorSpace K ℂ
  let ω := coordCx e b b'
  have hωc : ∀ w i, b'.equivFun (ω w) i = e (b.equivFun w i) := fun w i => coordCx_coord e b b' w i
  have hρ : ∀ γ w i, b.equivFun (ρ γ w) i = ∑ k, LinearMap.toMatrix b b (ρ γ) i k * b.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b (ρ γ) w) i
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hρ' : ∀ γ w i, b'.equivFun (ρ' γ w) i = ∑ k, e (LinearMap.toMatrix b b (ρ γ) i k) * b'.equivFun w k := by
    intro γ w i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b' b' (ρ' γ) w) i
    rw [hM γ] at this
    simp only [Module.Basis.equivFun_apply]; rw [← this]; rfl
  have hωρ : ∀ γ w, ω (ρ γ w) = ρ' γ (ω w) := fun γ w =>
    b'.equivFun.injective (funext fun i => by rw [hωc, hρ, hρ', map_sum]; simp only [map_mul, hωc])
  have hβ1 : ∀ (y : K) (z : ℂ) α, β.repr (e y * z) α = y * β.repr z α := by
    intro y z α
    rw [show e y * z = y • z from rfl, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let V := NX.TypeSpF L n K ρ J χ
  let v := Module.finBasis K V
  have hωV : ∀ f ∈ V, (fun g => ω (f g)) ∈ NG.TypeSp ρ' J (cx e χ) := by
    rintro f ⟨h1, h2⟩
    obtain ⟨N, hN0, hNc⟩ := hN
    refine ⟨⟨fun γ g => by simp only [h1, hωρ], N, hN0, fun κ hκ g => ?_⟩, fun κ => ?_⟩
    · obtain ⟨h, h1'⟩ := hNc κ hκ
      show ω (f (g * κ)) = ω (f g)
      have := h2 ⟨κ, h⟩ g
      rw [this, h1', Units.val_one, one_smul]
    · funext g
      show ω (f (g * κ)) = ((cx e χ κ : ℂˣ) : ℂ) • ω (f g)
      rw [h2, map_smulₛₗ, cx_apply]

  have hlinK : LinearIndependent K (fun j => ((v j : V) : GAf L n → W)) :=
    v.linearIndependent.map' V.subtype V.ker_subtype
  have hli : LinearIndependent ℂ (fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    rw [Fintype.linearIndependent_iff] at hlinK ⊢
    intro c hc j
    have hcoord : ∀ g i, ∑ j, c j * e (b.equivFun (((v j : V) : GAf L n → W) g) i) = 0 := by
      intro g i
      have := congrArg (fun F => b'.equivFun (F g) i) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul, hωc,
        Pi.zero_apply, map_zero] using this
    have hα : ∀ α, ∀ j, β.repr (c j) α = 0 := by
      intro α
      apply hlinK
      funext g
      apply b.equivFun.injective
      funext i
      have := congrArg (fun z => β.repr z α) (hcoord g i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, mul_comm (c _), hβ1, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at this
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, map_zero, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact β.repr.injective (by ext α; simp [hα α j])

  have hspanV : ∀ a : Fin (Module.finrank K V) → K,
      (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) ∈
        Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    intro a
    have : (fun g => ω ((∑ j, a j • ((v j : V) : GAf L n → W)) g)) =
        ∑ j, e (a j) • fun g => ω (((v j : V) : GAf L n → W) g) := by
      funext g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smulₛₗ]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hspan : NG.TypeSp ρ' J (cx e χ) = Submodule.span ℂ (Set.range fun j => fun g => ω (((v j : V) : GAf L n → W) g)) := by
    refine le_antisymm ?_ (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hωV _ (v j).2))
    rintro F ⟨⟨hF1, -⟩, hF2⟩
    have hFk : ∀ (κ : J) g, F (g * κ) = e (χ κ) • F g := fun κ g => congrFun (hF2 κ) g
    let fa : _ → GAf L n → W := fun α g => b.equivFun.symm fun i => β.repr (b'.equivFun (F g) i) α
    have hfa : ∀ α g i, b.equivFun (fa α g) i = β.repr (b'.equivFun (F g) i) α := by
      intro α g i; simp only [fa, LinearEquiv.apply_symm_apply]
    have hfaV : ∀ α, fa α ∈ V := by
      intro α
      refine ⟨fun γ g => b.equivFun.injective (funext fun i => ?_), fun κ g => b.equivFun.injective (funext fun i => ?_)⟩
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hfa, hF1, hρ', hρ, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
          simp only [hβ1, hfa]
      · rw [hfa, hFk]
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, hβ1, hfa]
    obtain ⟨P, hP⟩ := exists_finset_eval_eq_zero V
    let S := P.biUnion fun g => Finset.univ.biUnion fun i => (β.repr (b'.equivFun (F g) i)).support
    have hzero : ∀ α ∉ S, fa α = 0 := by
      intro α hα
      refine hP _ (hfaV α) fun g hg => b.equivFun.injective (funext fun i => ?_)
      rw [hfa, map_zero, Pi.zero_apply]
      by_contra h
      exact hα (Finset.mem_biUnion.2 ⟨g, hg, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.2 h⟩⟩)
    have hsub : ∀ g i, (β.repr (b'.equivFun (F g) i)).support ⊆ S := by
      intro g i α hα
      by_contra hS
      have := congrArg (fun f => b.equivFun (f g) i) (hzero α hS)
      simp only [hfa, Pi.zero_apply, map_zero] at this
      exact (Finsupp.mem_support_iff.1 hα) this
    have hFeq : F = ∑ α ∈ S, β α • fun g => ω (fa α g) := by
      funext g
      apply b'.equivFun.injective
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul, hωc, hfa]
      conv_lhs => rw [← β.linearCombination_repr (b'.equivFun (F g) i)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsub g i) (fun a c => c • β a) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun α _ => mul_comm _ _
    rw [hFeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    have hrep := congrArg Subtype.val (v.sum_repr ⟨fa α, hfaV α⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep]
    exact hspanV _
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.LevCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.Mem.PdNotType

theorem pD_not_type : ∀ (D : D7) (i : D.ntw.Tw) (P : PlE D.host) (k : Fin 2), P ∈ D.ntw.pD i →
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro D i P k hP
  intro hg
  have hPs : P ∈ (D.ntw.pD i : Set (HeightOneSpectrum (𝓞 D.host.E))) := hP
  rw [D.ntw.pD_eq i] at hPs
  have hPg : P ∈ placesOver D.host.E (D.host.g k) := by
    simpa [placesOver] using hg
  split_ifs at hPs
  · exact GlobalTheory.InertialTypes.not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 hPs hPg
  · exact GlobalTheory.InertialTypes.not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 hPs hPg

end GlobalTheory.Mem.PdNotType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

section Gen

variable {D : D7} (N : TwNew D)

theorem goodL_eq (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    goodL N.toD7 (N.rat S) θ j = goodL D S θ j := by
  have h : N.ex.eLL0 = D.nexp.eLL0 := funext fun g =>
    Subtype.ext (D.what₂.embLL.injective ((N.h0 g).trans (D.nStage_trivialCharacter_coeff_eq g).symm))
  exact congrArg (fun e : G0g D.nd → ↥D.LL0 =>
    Module.End.eigenspace (∑ᶠ g : G0g D.nd, ((e g : ↥D.LL0) : D.what₂.LL) • actL D S j g) 1 ⊓
    ⨅ u : Formalism.IndefR.NX.U D.nd, Module.End.eigenspace (actL D S j u)
      (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) h

def ratIn {S : RatDat D.ntw} (I : RatIn D S) : RatIn N.toD7 (N.rat S) where
  Sb := I.Sb
  rho := I.rho
  chi := I.chi
  ks := I.ks
  fd := I.fd
  mk_fg := I.mk_fg
  hL := I.hL
  hs := I.hs
  hL_zero := I.hL_zero
  θ := I.θ
  θ_ne := I.θ_ne
  eig := I.eig
  span := fun j h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.span j h1 h2
  hL_int := fun j k P h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.hL_int j k P h1 h2

theorem cusp {Rw : RowSide D} (h : RowCusp D Rw) : RowCusp N.toD7 (N.row Rw) := h

theorem mtIn {M tup Q} (h : MtInput D M tup Q) : MtInput N.toD7 (N.mt M) tup Q := { h with }

end Gen

end GlobalTheory.HeightCounting.Up.LiTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QPlacesOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ParaPlace

theorem unr_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : χ'.UnrAt u) : (χ * χ').UnrAt u := fun y hy => by
  change χ.loc u y * χ'.loc u y = 1
  rw [h y hy, h' y hy, one_mul]

end GlobalTheory.LevCmp.ParaPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
section
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowRatW_of_rowTest :
    (AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → RowRatW :=
  by
    intro H
    have h := (StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans H
    apply h.trans
    apply StepW.of_all
    intro K B f T w hK hF G Z hX Wt z a b _ c d _ _ _ _
    exact G Z hX Wt z a b c d

end GlobalTheory.Mem.LiteralAutomorphy
end

