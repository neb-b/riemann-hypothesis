module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstMapInjective
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsAllLifts
section
noncomputable section

namespace GlobalTheory.Mem.GJModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_place (B : Base) {l : ℕ} (hl : l.Prime) : ∃ w : B.places.Pl, B.places.resChar w = l := by
  have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 B.LL)
    (Ideal.span {((l : ℕ) : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 B.LL)).injective_int]
      exact bot_le)
  have hmem : ((l : ℕ) : 𝓞 B.LL) ∈ P := by
    have : ((l : ℕ) : ℤ) ∈ P.comap (algebraMap ℤ (𝓞 B.LL)) := by
      change ((l : ℕ) : ℤ) ∈ Ideal.under ℤ P
      rw [hPl]; exact Ideal.mem_span_singleton_self _
    simpa using this
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hl.ne_zero (by exact_mod_cast hmem)
  let w : HeightOneSpectrum (𝓞 B.LL) := ⟨P, hP.isPrime, hne⟩
  exact ⟨w, Examples₂.PlacesToy.prime_mem_unique w (Examples₂.PlacesToy.resCharW_prime w) hl
    (Examples₂.PlacesToy.resCharW_mem w) hmem⟩

theorem tau_nonempty (B : Base) : Nonempty (Tau B.R) := by
  rw [← Fintype.card_pos_iff, card_Tau B.host]
  unfold Ranks.f Ranks.n
  have := B.R.ord_pos
  omega

theorem exists_inert {R : Ranks} (H : Host R) :
    ∃ l : ℕ, l.Prime ∧ 5 ≤ l ∧ (H.cls l = .signal ∨ H.cls l = .inertClass) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  obtain ⟨l, hgt, hl, hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (5 + H.q + H.d + H.QS) (q := 4 * H.d) (a := -1)
    (by have := hd.pos; omega) isCoprime_one_left.neg_left
  have h4 : l % 4 = 3 := by
    have : (l : ℤ) ≡ -1 [ZMOD 4] := hmod.of_dvd ⟨H.d, by push_cast; ring⟩
    unfold Int.ModEq at this
    omega
  have hd4 : H.d % 4 = 3 := by omega
  have hmd : (l : ℤ) % (H.d : ℤ) = (-1) % (H.d : ℤ) := hmod.of_dvd ⟨4, by push_cast; ring⟩
  have hj : jacobiSym (-(H.d : ℤ)) l = -1 := by
    rw [show (-(H.d : ℤ)) = -1 * (H.d : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)), jacobiSym.quadratic_reciprocity_three_mod_four hd4 h4,
      jacobiSym.mod_left' hmd, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)),
      ZMod.χ₄_nat_three_mod_four h4, ZMod.χ₄_nat_three_mod_four hd4]
    norm_num
  refine ⟨l, hl, by omega, ?_⟩
  have hs : l ∉ H.small := fun h => by
    have := Nat.le_of_mem_primeFactors h
    omega
  unfold Host.cls primeClass
  rw [if_neg hs, if_neg (by omega), if_neg (by omega), if_neg (by rw [hj]; norm_num)]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_of_jet (B : Base) (C : Cols B) (vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ)
    (hvol : ∀ W, 0 < vol W) (cd : CDHaar) (jet : ThetaJet B.R B.host) (gx : GlobalExtra B.LL (Tau B.R))
    (h : ∀ i, ∃ u, Nonempty ((C.mem u).C.cls (jet.jOf i - 1)) ∧ Nonempty ((C.mem u).C.cls (jet.jOf i)))
    (h1 : ∀ i, ∃ u, Nonempty ((C.mem u).C.cls (jet.j1Of i - 1)) ∧ Nonempty ((C.mem u).C.cls (jet.j1Of i))) :
    ∃ G : GJStage B C, G.vol = vol ∧ G.cd = cd ∧ G.jet = jet ∧ G.gx = gx ∧
      ∀ u w h, (G.gat u w h).FinClasses := by
  choose U hU hU' using h
  choose U1 hU1 hU1' using h1
  choose w hw using fun i : jet.Sit => exists_place B (jet.loc i).hl.out
  choose w1 hw1 using fun i : jet.Sit1 => exists_place B (jet.loc1 i).hl.out
  obtain ⟨τ⟩ := tau_nonempty B
  choose g hg hg' using fun (u : B.Word) (v : B.places.Pl)
      (hh : GIdx B.host (C.mem u).A.T (B.places.resChar v)) =>
    GlobalTheory.PrescribedRank.GAtP₂ (B.places.resChar v) (Module.finrank ℂ (C.mem u).A.Mu0) hh.1
  exact ⟨{ vol := vol, vol_pos := hvol, cd := cd, jet := jet, jetU := U
           jetL := fun i => (hU i).some, jetL' := fun i => (hU' i).some
           jetW := w, jetW_l := hw, jetTau := fun _ _ => τ
           jetW1 := w1, resChar_thetaJetPlaceDegOne := hw1, jetTau1 := fun _ => τ, jetU1 := U1
           jetL1 := fun i => (hU1 i).some, jetL1' := fun i => (hU1' i).some
           gx := gx, gat := g, gat_d := hg }, rfl, rfl, rfl, rfl, hg'⟩

def gxOne (B : Base) : GlobalExtra B.LL (Tau B.R) :=
  ⟨fun _ _ => 1, fun _ _ => one_pos, fun _ => 1, fun _ => one_pos⟩

end GlobalTheory.Mem.GJModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure PreChar : Prop where
  lev : R.toLevCh.Is A.μ0
  red_R : R.grp_red_R
  red_L : R.grp_red_L
  record : R.grp_record
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP

def ValKs : Prop :=
  ∀ (i : Fin D.R.m) (x : (AE D)ˣ), infPart D (x : AE D) = 1 →
    ∃ y : Ks, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y)

def FrameKs (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL]
    (MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ)) : Prop :=
  (∀ i σ σ', σ.comp (algebraMap Ks D.what₂.LL) = σ'.comp (algebraMap Ks D.what₂.LL) →
    ∀ ρ, x0Mat (MW i σ) ρ = x0Mat (MW i σ') ρ) ∧
  ∀ i σ, (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) →
    ∀ τ a, (MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)

def LevKs (F : Face D A) : Prop :=
  (∀ p, ((F.ψ0 p : D.what₂.LLˣ) : D.what₂.LL) ∈ (algebraMap Ks D.what₂.LL).range) ∧
    ∀ g, (idemOf A.X).coeff g ∈ (algebraMap Ks D.what₂.LL).range

structure MjTie (F : Face D A) where
  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H
  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e
  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2
  eW_lat : ∀ (i : Fin D.R.m) x, x ∈ (D.what₂.MjLat ((i : ℕ) + 1)).carrier ↔
    ∃ y ∈ (R.FW i).MK, y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) ∧ eW i x = (R.FW i).j (sg0 D A) y

end Data

abbrev reCore (T : CoreJ D) (dict : ∀ j σ, GA D (T.V j σ) → Σ k, Frame ((T.U j σ).X k).Ψ D.R.r)
    (mu : ∀ j σ, GA D (T.V j σ) → ℂ) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (cE : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D :=
  { Q := T.Q, U := T.U, V := T.V, dict := dict, mu := mu, Kf := T.Kf, pb := T.pb, cE := cE, chiW := chiW, x₀ := x₀,
    iota := T.iota }

abbrev setCE (T : CoreJ D) (cE : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D :=
  reCore T T.dict T.mu T.chiW T.x₀ cE

section Forms

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))


open Classical in
def geoRho (i : Fin D.R.m) : G →* ((Fin (nTop T κ i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (nTop T κ i) → D.what₂.LL)) :=
  if h : HasB T.Q.c.F (Cu T κ i) (nTop T κ i) ∧ ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i),
      ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))
  then rhoB D.what₂.LL h.1.some h.2.choose else 1

def formsGeo (i : Fin D.R.m) :
    Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nTop T κ i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G :=
  { formsN T R κ v₀ i (nTop T κ i) with ρ := geoRho T R κ O i }

abbrev geoR : RealDat D A T.Q.c.F := updFW R (nTop T κ) (formsGeo T R κ v₀ O)

def Fired (ph : Fin D.R.m → ℂ) : Prop :=
  (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) (ph i)) ∧
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)

end Forms


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure GeoHalf (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) : Type 1 where
  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)
  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec
  fw : FWTie T R κ v₀
  bar : BarTie fw
  O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)
  pins : ∀ i, OMPins T R κ v₀ O i
  rhoGeo : RhoGeo fw O
  equivAll : EquivAll T R κ O
  cTie : ∀ i, CTie T R κ v₀ O i
  phase : ∀ i, R.LUnif → PhaseTie T R κ v₀ O ph i

structure InGeo {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GeoHalf T R ph) : Prop where
  jEvExists : JEvExists T R B.κ B.v₀
  jEvBar : JEvBar T R B.κ
  evInj : EvInj T R B.v₀
  jUnif : JUnif T R B.κ B.v₀
  geoAct : GeoAct T R B.κ B.v₀
  latFull : LatFull T B.κ
  dimMatch : DimMatch T R B.κ

end GlobalTheory.RealGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure LocStage where
  loc : LocTheory
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)

structure NStage (B : Base) (C : Cols B) (W : RowsRest B C) extends LocStage where
  nd : NData B.R B.host W.what₂
  ntw : NTw B.R B.host W.what₂ B.LL0 nd
  naut : NAut nd
  nbc : NBC naut
  nexp : NExp B.R B.host W.what₂ B.LL0 nd ntw
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, B.embLL ((nexp.eLL0 g : ↥B.LL0) : B.LL) = ntypes.e0.coeff g
  nth : NTh B.R B.host W.what₂ B.LL0 nd ntw nexp
  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)), w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) B.host.E nd.Om (ReciprocityTheory.Gal.Dec (F := B.host.E) (nd.plOm.1 w)) (nd.O i)
  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef B.host.condN (nbr i w hw).LL
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 B.host.E)), w ∈ Formalism.BasicNotions.placesOver B.host.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) B.host.E nd.Om (ReciprocityTheory.Gal.Dec (F := B.host.E) (nd.plOm.1 w)) (ntw.O0 i)
  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes
  Z_tie : ∀ i x, x ∈ nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN nd naut i
  Zgood_tie : ∀ i x, x ∈ nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN nd naut i
  etaJ_tie : ∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = ∑ i ∈ nd.locs j w, nd.etaLoc i

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure DivStage (B : Base) (C : Cols B) (W : RowsRest B C) where
  div : DivData B.LL B.Word
  div_good : (∀ v, IsUnit (div.RR.X v).det) ∧ ∀ u v, IsUnit ((div.Nu u).X v).det
  jEE : div.RR.V →ₛₗ[B.embLL] W.EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (div.RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (div.RR.b i))) = ⊤
  jN : ∀ u, (div.Nu u).V →ₛₗ[B.embLL] W.Mu u
  jN_basis : ∀ u, LinearIndependent ℂ (fun i => jN u ((div.Nu u).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jN u ((div.Nu u).b i))) = ⊤
  Dall_eq : div.Dall = W.Dall
  delP_eq : div.delP = W.delp
  nuIn : ∀ u, (div.Nu u).V →ₗ[B.LL] ((C.fm u).lat 0).V
  nuIn_inj : ∀ u, Function.Injective (nuIn u)
  nuIn_range : ∀ u, LinearMap.range (nuIn u) = (C.fm u).ramSub
  nuIn_jN : ∀ u (x : (div.Nu u).V),
    ((W.eMu u (jN u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = (C.fm u).emb 0 (nuIn u x)
  nuIn_norm : ∀ u v (x : (div.Nu u).V), Formalism.HermitianLatticesTheory.normAt (div.Nu u).b (div.Nu u).X v x =
    Formalism.HermitianLatticesTheory.normAt ((C.fm u).lat 0).b ((C.fm u).lat 0).X v (nuIn u x)
  jEE_norm : ∀ x : div.RR.V,
    Formalism.HermitianLatticesTheory.normAt div.RR.b div.RR.X (InfinitePlace.mk B.embLL) x = ‖jEE x‖

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SCuIsom
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure SStage (B : Base) (C : Cols B) (W : RowsRest B C) where
  dsig : (Tau B.R) → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ
  s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW
  s_split : ∀ p, (s.atP p).split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  s_HH : Module.finrank ℂ s.HH = W.Dall
  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (C.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 B.host.F)
  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (C.fm u).ipC 0 ((s_Cu u x : (C.mem u).A.Mu0) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (C.mem u).A.Mu0) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
  sEE : W.EE →ₗᵢ⋆[ℂ] s.HH

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WithTrue
section
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def GJStage.withTrue {B : Base} {C : Cols B} (G : GJStage B C) : GJStage B C :=
  letI := B.host.cmStar
  { G with
    vol := fun W => Vol.trueVol B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    vol_pos := fun W => Vol.trueVol_pos B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    gx := Per.trueGx B.host B.embLL B.embE (Equiv.refl _) }

end GlobalTheory.Mem
end
end

