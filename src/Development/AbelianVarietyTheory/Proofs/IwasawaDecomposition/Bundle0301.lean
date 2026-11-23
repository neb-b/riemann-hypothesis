module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Formalism.LocalToGlobal.Columns.TiedLv
public import Formalism.LocalToGlobal.Columns.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

abbrev recOf (Z : Later B C) : D7 := assemble B C Z.W Z.V Z.S Z.N Z.G

variable {Z : Later B C} (Z' : Later B C)


set_option maxHeartbeats 4000000 in
def atTTRe {u : B.Word} (A : AtTTied (D := recOf Z) u) : AtTTied (D := recOf Z') u := { A with }


set_option maxHeartbeats 4000000 in
def clsRe {u : B.Word} {i : ℕ} {hi : i ≤ B.R.m} (K : ClsTied (D := recOf Z) u i hi) : ClsTied (D := recOf Z') u i hi := { K with }


set_option maxHeartbeats 4000000 in
def valRe {u : B.Word} {eV : (C.mem u).A.vT ≃ PlT (recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} {K : ClsTied (D := recOf Z) u i hi}
    (W : ValTied (D := recOf Z) u eV i hi K) : ValTied (D := recOf Z') u eV i hi (clsRe Z' K) := { W with }


set_option maxHeartbeats 4000000 in
def lvRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} (P : LvTied (D := recOf Z) u A i hi) :
    LvTied (D := recOf Z') u (atTTRe Z' A) i hi := { P with }


set_option maxHeartbeats 4000000 in
def clsPRe {u : B.Word} (K : ClsPTied (D := recOf Z) u) : ClsPTied (D := recOf Z') u := { K with }


set_option maxHeartbeats 4000000 in
def valPRe {u : B.Word} {K : ClsPTied (D := recOf Z) u} (W : ValPTied (D := recOf Z) u K) :
    ValPTied (D := recOf Z') u (clsPRe Z' K) := { W with }


set_option maxHeartbeats 4000000 in
def tilRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    (Tl : TilTied (D := recOf Z) u A K P) : TilTied (D := recOf Z') u (atTTRe Z' A) (clsPRe Z' K) (lvRe Z' P) := { Tl with }


set_option maxHeartbeats 4000000 in
def tilAdRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    {Tl : TilTied (D := recOf Z) u A K P} {Km : ClsTied (D := recOf Z) u B.R.m le_rfl} (Ta : TilAd (D := recOf Z) Tl Km) :
    TilAd (D := recOf Z') (tilRe Z' Tl) (clsRe Z' Km) := { Ta with }


set_option maxHeartbeats 4000000 in
def chartRe {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {i : ℕ} {hi : i ≤ B.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (K : LevelChart (recOf Z) T bad i hi stab lat) : LevelChart (recOf Z') T bad i hi stab lat := { K with }


set_option maxHeartbeats 4000000 in
def lvGRe {u : B.Word} {T : ℕ} {res : ∀ v : (C.mem u).A.vT, 𝓞 B.host.E →+* (C.mem u).A.Fv v} {i : ℕ} {hi : i ≤ B.R.m}
    {lat : (C.mem u).C.cls i → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (L : LevelCompatibleLattices (D := recOf Z) (u := u) (C.fm u) T res i hi lat) : LevelCompatibleLattices (D := recOf Z') (u := u) (C.fm u) T res i hi lat := { L with }


set_option maxHeartbeats 16000000 in
def formsRe {u : B.Word} {Ch : ℕ → Type} {chOf : ∀ i, (C.mem u).C.cls i → Ch i} (T : FormsTiedSym (recOf Z) u Ch chOf) :
    FormsTiedSym (recOf Z') u Ch chOf :=
  { T with
    atT := atTTRe Z' T.atT
    cls := fun i hi h => clsRe Z' (T.cls i hi h)
    val := fun i hi h => valRe Z' (T.val i hi h)
    lv := fun i hi => lvRe Z' (T.lv i hi)
    ch := fun i h1 h2 β => chartRe Z' (T.ch i h1 h2 β)
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => lvGRe Z' (T.lvC i h1 h2)
    clsP := clsPRe Z' T.clsP
    valP := valPRe Z' T.valP
    til := tilRe Z' T.til
    tilAd := tilAdRe Z' T.tilAd }


set_option maxHeartbeats 4000000 in
def hermChRe (H : Formalism.L2.Herm.HermColsCh (recOf Z)) : Formalism.L2.Herm.HermColsCh (recOf Z') := { H with }


set_option maxHeartbeats 4000000 in
def atTRe {u : B.Word}
    {e : (C.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 B.host.F) // (((C.mem u).A.T : ℕ) : 𝓞 B.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (C.mem u).A.vT, (C.mem u).A.Fv v ≃+* (𝓞 B.host.F ⧸ (e v).1.asIdeal)} (A : Formalism.L2.Herm.AtT (recOf Z) u e eF) :
    Formalism.L2.Herm.AtT (recOf Z') u e eF := { A with }


set_option maxHeartbeats 4000000 in
def hermRe (H : Formalism.L2.Herm.ColsHermS (recOf Z)) : Formalism.L2.Herm.ColsHermS (recOf Z') :=
  { H with
    base := hermChRe Z' H.base
    atT := fun u => atTRe Z' (H.atT u)
    ad := { H.ad with } }


set_option maxHeartbeats 16000000 in
def colsRe (T : ColsTiedSym (recOf Z)) : ColsTiedSym (recOf Z') :=
  { T with
    herm := hermRe Z' T.herm
    forms := fun u => formsRe Z' (T.forms u)
    gl_const := T.gl_const }

end GlobalTheory.Mem.Top.ColOwe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevel
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
noncomputable section

namespace GlobalTheory.ConjRowLevelSee

theorem conjMap_level_of_seeAt : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ _ _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t _ _ _ _ _ hsee c _ Φ hΦ hrep u (k : GA D (D.sp.Y 0)) hk (g : GA D (D.sp.Y 0))
  obtain ⟨ψ, hψ⟩ := hrep u
  show star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))))) = _ *
    star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)))
      (iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0)))))
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hJ, hχ⟩ := hsee.conj k
  have hmem := hJ.1 hk
  have hval := hχ hk
  set x := iotaX X h ((t⁻¹)⁻¹ * k * t⁻¹ : GA D (D.sp.Y 0)) with hxdef
  have hx : x.1 = 1 ∧ x.2 ∈ X.K2 := hmem
  have hxeq : x = (1, x.2) := Prod.ext hx.1 rfl
  have hΦk : X.B.R (1, x.2) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
      X.chi2 x.2 • Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
    obtain ⟨T', -, hT'⟩ := hΦ
    rw [← hT']
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (T' _)) (GlobalTheory.ConjRowLevel.reg_comp_Re X x.2 hx.2)
  have hrep2 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (1, x.2)
  rw [hΦk] at hrep2
  have key := Formalism.L2.SG.EvalTOntoRep.contRep_unique X hrep2 (Formalism.L2.SG.EvalTOntoRep.contRep_smul X _ hψ)
  have e1 : (g * k * t⁻¹ : GA D (D.sp.Y 0)) = g * t⁻¹ * ((t⁻¹)⁻¹ * k * t⁻¹) := by group
  have hkey : ∀ z, ψ (z * x) = X.chi2 x.2 * ψ z := by
    intro z
    conv_lhs => rw [hxeq]
    exact congrFun key z
  have hm : iotaX X h ((g * k * t⁻¹ : GA D (D.sp.Y 0))) = iotaX X h ((g * t⁻¹ : GA D (D.sp.Y 0))) * x := by
    rw [e1, hxdef]
    exact map_mul (iotaX X h) _ _
  rw [hm, hkey, star_mul']
  exact congrArg (· * _) hval

end GlobalTheory.ConjRowLevelSee
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwAtStd

theorem ptY_mv_deco {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}
    (p : PtY ST SG Q y) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    (h1 : ∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) (h2 : p.1.2 ∈ y.ys d.1.N) :
    (p.mv d).1.1.deco = d := by
  have e : p.mv d = (⟨(⟨(d, p.1.1.1.2), h1⟩, p.1.2), h2⟩ : PtY ST SG Q y) := dif_pos ⟨h1, h2⟩
  rw [e]
  rfl

theorem diaPt_deco (B : Base) (X : PreX B.toPre) (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u a i).Cl) :
    (((I.atIn u a).A i).diaPt P x c).1.1.deco = DecoSet.dia1 P x ((I.stp u a i).rep c).1.1.deco :=
  ptY_mv_deco ((I.stp u a i).rep c) _ (fun Q y => ((I.stp u a i).rep c).1.1.2 Q y) ((I.stp u a i).rep c).2

theorem dil_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dil 0 P x (I.eCls0 l u a c) = I.eCls0 l u a ((I.atIn u I.mu0).dil 0 P x c) := by
  show (I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) =
    I.cl0 u a (l.idx0 a).some ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  refine (ClsZero.cl_eq_iff hI u a _ _ _ _).2 ?_
  rw [diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have e := (ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1
    (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c)))
  show _ = ClsZero.canon _ ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco
  rw [e, diaPt_deco]

theorem deco_stab_trivial (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b) (γ : UF B.fields.E (B.R.N 0)) (k : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))
    (hk : k ∈ (colLev I.Ch 0).grp) (h : ((γ, k) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • p.1.1.deco = p.1.1.deco) :
    γ = 1 ∧ k = 1 := by
  have hfree : (I.stp u a 0).Free := (l.lev u a).free0
  let q : DecoF B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a)) :=
    ((γ, k, 1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) • p.1.1
  have hq : q.deco = p.1.1.deco := h
  have hc : ∀ P : QE I.sel (I.tup a), (p.1.1.fr P)⁻¹ * q.fr P ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    have h1 := q.2 P x
    have h2 := p.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x))
    have h3 : p.1.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
    rw [h3] at h2
    have h4 : q.1.1 = p.1.1.1.1 := hq
    rw [h4] at h1
    exact h2.symm.trans h1
  have hkG : k ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b).grp := by rw [ClsZero.levelTypePrimes_stepZero_eq_colLev hI]; exact hk
  let qq : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a)) := fun P => ⟨(p.1.1.fr P)⁻¹ * q.fr P, hc P⟩
  have htop : ∀ Θ : LevQFam B.fields.E B.fields.K (B.R.N 0) (QE I.sel (I.tup a)), Θ = LevQFam.top _ _ _ _ → qq ∈ Θ.grp := by
    rintro _ rfl
    intro P _
    trivial
  have hqQ := htop _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a b)
  have key : ∀ (y : Ys B.fields (B.R.N 0)), y = Ys.triv _ _ → ∀ (S : Set (Sp B.fields.E (B.R.N 0))) N, S ∈ y.ys N → S = ∅ := by
    rintro _ rfl S N hS
    exact hS
  have hp0 : p.1.2 = ∅ := key _ (ClsZero.ys0 a) _ _ p.2
  let g : (I.stp u a 0).G b := (γ, ⟨k, hkG⟩, ⟨qq, hqQ⟩)
  have hg : (I.stp u a 0).act b g p = p := by
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) P)⁻¹.1))⁻¹ = p.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · show (fun v => γ.1 v) '' p.1.2 = p.1.2
      rw [hp0, Set.image_empty]
  have e := hfree b g p hg
  exact ⟨congrArg Prod.fst e, congrArg (fun g : (I.stp u a 0).G b => (g.2.1 : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) e⟩

theorem chrG_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (L Λ Λ' : LevFam E K n SG) (h : Λ = L) (h' : Λ' = L) (k : Λ.grp) (k' : Λ'.grp) (e : k.1 = k'.1) :
    Λ.chr k = Λ'.chr k' := by
  subst h h'
  rw [Subtype.ext e]

theorem chrQ_top {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}
    (Θ : LevQFam E K n Q) (h : Θ = LevQFam.top E K n Q) (q : Θ.grp) : Θ.chr q = 1 := by
  subst h
  unfold LevQFam.chr piChar
  erw [Finset.prod_eq_one (fun i _ => MonoidHom.one_comp _)]
  rfl

theorem dilT_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dilT B.fields.emb B.embLL 0 P x (I.eCls0 l u a c) = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 P x c := by
  show (I.stp u a 0).tr B.fields.emb B.embLL (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c))) = (I.stp u I.mu0 0).tr B.fields.emb B.embLL c.1 ((I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  set ga := (I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) with hga
  set gm := (I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c) with hgm
  have hA : ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    congrArg (fun p : (I.stp u a 0).D (I.cl0 u a (l.idx0 a).some c).1 => p.1.1.deco) ((I.stp u a 0).mv_smul (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))
  have hM : ((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    congrArg (fun p : (I.stp u I.mu0 0).D c.1 => p.1.1.deco) ((I.stp u I.mu0 0).mv_smul c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  have hRA : ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u a _).trans ((ClsZero.cl_eq_iff hI u a _ _ _ _).1 (ClsZero.cl_rep (I.stp u a 0) ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))))
  have hRM : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u I.mu0 _).trans ((ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1 (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))))
  have hT : (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco := by
    rw [diaPt_deco, diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have hR : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by rw [hRA, hRM, hT]
  rw [hR, ← hT] at hM
  have hfix : (((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))⁻¹ *
      ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by
    rw [mul_smul, hA, inv_smul_eq_iff, hM]
  have memG : ∀ Λ : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs, Λ = colLev I.Ch 0 → ∀ k : Λ.grp, k.1 ∈ (colLev I.Ch 0).grp := by
    rintro _ rfl k
    exact k.2
  have hkA := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) ga.2.1
  have hkM := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) gm.2.1
  obtain ⟨e1, e2⟩ := deco_stab_trivial B X I hI l u a (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))) (gm.1⁻¹ * ga.1) (gm.2.1.1⁻¹ * ga.2.1.1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkM) hkA) hfix
  have eγ : ga.1 = gm.1 := (inv_mul_eq_one.1 e1).symm
  have ek : ga.2.1.1 = gm.2.1.1 := (inv_mul_eq_one.1 e2).symm
  show trFr B.fields.emb B.embLL ((I.stp u a 0).gam (I.cl0 u a (l.idx0 a).some c).1 ga) ((I.stp u a 0).chr (I.cl0 u a (l.idx0 a).some c).1 ga) = trFr B.fields.emb B.embLL ((I.stp u I.mu0 0).gam c.1 gm) ((I.stp u I.mu0 0).chr c.1 gm)
  congr 1
  · show ufGL _ _ ga.1 = ufGL _ _ gm.1
    rw [eγ]
  · show (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.2 =
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.1 * (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.2
    rw [chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a _), chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 _),
      chrG_eq (colLev I.Ch 0) _ _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) ga.2.1 gm.2.1 ek]

theorem mem_Fi_of_free {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (hS : S.Free)
    (φ : S.Cl → Col2.Fr emb σ n → ℂ) : φ ∈ S.Fi emb σ lam ↔ ∀ c, φ c ∈ ValC (Gr emb σ n) lam := by
  constructor
  · intro h c
    exact (h c).1
  · intro h c
    refine ⟨h c, fun g => ?_⟩
    have hg : g.1 = 1 := hS c.1 g.1 _ g.2
    funext y
    show S.tr emb σ c.1 g.1 (φ c) y = φ c y
    rw [hg]
    simp [GStep.tr, trFr_apply, frMul_one]


set_option maxHeartbeats 1000000 in
theorem twAtT_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ t : TwAtT (I.tw l l0 Z) u a, t.eVT = Equiv.refl _ ∧ ∀ v (r : 𝓞 B.host.E), t.eFv v (I.resT l u a v r) = I.resT l u I.mu0 (t.eVT v) r := by
  intro B X I hI hP l Z l0 u a
  refine ⟨
    { eVT := Equiv.refl _
      eFv := fun v => RingEquiv.refl _
      psiT := fun v x => rfl
      rhoT := by
        intro v x φ
        have e1 := dil_eCls0 B X I hI l u a v x
        have e2 := dilT_eCls0 B X I hI l u a v x
        funext c y
        obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
        show (I.atIn u a).dilT B.fields.emb B.embLL 0 v x (I.eCls0 l u a c') (φ ((I.eCls0 l u a).symm ((I.atIn u a).dil 0 v x (I.eCls0 l u a c')))) y = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')) (φ ((I.atIn u I.mu0).dil 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')))) y
        simp only [e1, e2, Equiv.symm_apply_apply]
      Mu0 := by
        show (I.stp u a 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) = Submodule.map (LinearEquiv.funCongrLeft ℂ (Col2.Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) (I.eCls0 l u a).symm).toLinearMap ((I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0))
        rw [Submodule.map_equiv_eq_comap_symm]
        ext ψ
        rw [Submodule.mem_comap, mem_Fi_of_free _ _ _ _ (l.lev u a).free0, mem_Fi_of_free _ _ _ _ (l.lev u I.mu0).free0]
        constructor
        · intro h c
          exact h _
        · intro h c
          obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
          have := h c'
          simpa using this
      duStar := rfl
      Dstar := rfl
      GamP := rfl
      tauOf := fun w hw v => rfl
      seenP := fun w hw => rfl }, rfl, fun v r => rfl⟩

end GlobalTheory.Mem.Col2.TwAtStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownMoveLocalDualLatticeEqLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnLat

theorem locP_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : p = q) (L : Submodule R W) : Formalism.HermitianLatticesTheory.localization₂ p L = Formalism.HermitianLatticesTheory.localization₂ q L := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem extF_eq (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E))
    (g : Module.Dual (Res P) (TDat.Red M P)) (y : Fin n → E) : TDat.extF M P g y = modP.ext P M g y := by
  classical
  unfold TDat.extF
  split_ifs with h
  · obtain ⟨s, hs, z, hz, hgz⟩ := h.choose_spec
    have hsy : s • y ∈ M := hz ▸ z.2
    have e := modP.ext_spec P M g y hs hsy
    have ez : z = ⟨s • y, hsy⟩ := Subtype.ext hz
    subst ez
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [e, ← hgz]
    rfl
  · by_cases hy : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M
    · exfalso
      obtain ⟨s, hs, hsy⟩ := hy
      exact h ⟨modP.ext P M g y, s, hs, ⟨s • y, hsy⟩, rfl, (modP.ext_spec P M g y hs hsy).symm⟩
    · unfold modP.ext
      rw [dite_eq_right hy]

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem ok_dn_extF {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : M = d.dnN P) (g : Module.Dual (Res P.1) (TDat.Red M P.1)) (hg : g ≠ 0) :
    (d.dn P (TDat.extF M P.1 g)).Ok := by
  subst hM
  have e : TDat.extF (d.dnN P) P.1 g = modP.ext P.1 (d.dnN P) g := funext (extF_eq _ _ g)
  rw [e]
  have hF := modP.ext_funAt P.1 (d.dnN P) g
  refine hd.dn P hP hF.add hF.smul hF.off ?_
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra H
    push Not at H
    exact hg (LinearMap.ext H)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x.1, x.2, by rw [modP.ext_of_mem]; exact hz⟩

theorem locP_Lsh_dn {a : 𝓞 E} (ha : SepElt ST a) {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    {f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal} (hd' : (d.dn P f').Ok) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dn P f').Lsh = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L := by
  rw [hd'.locP_Lsh ha P]
  show Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dnN P) = _
  rw [(hd.dnN_spec P hne).2.2.2, tud_locP_L ha ⟨d, hd⟩ P]
  exact le_antisymm
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact lv_kerAt_le ⟨d, hd⟩ ha P hx)
    (localization_le_of_smul_mem (ha.off P) fun x hx => lv_smul_LshKer_mem ⟨d, hd⟩ ha P hx)

theorem mulLat_Lsh_rep {K : Type} [Field K] [NumberField K] [StarRing K] (S : GStep E K n) (hS : S.Ok) (b : S.β) (d : S.D b)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : γ = (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E)) :
    Formalism.L2.Forms.mulLat γ (S.Lsh b (S.rep (S.cl b d))) = S.Lsh b d := by
  subst hγ
  ext x
  unfold Formalism.L2.Forms.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) y).2 hy
    rwa [S.mv_smul] at h
  · intro hx
    refine ⟨((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x, ?_, ?_⟩
    · refine (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) _).1 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, S.mv_smul]
      exact hx
    · show (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.DnLat


open GlobalTheory.Mem.Col2.DnLat in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Col2.TC.dn_locP_lat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (mulLat γ.1.1 (LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) = Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ
  obtain ⟨hg1, -, hcrd⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hlat := (hcrd u a).1
  have hPv : PvG (D := I.rec7 l Z) (I.resT l u a) v = (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    unfold PvG resT
    ext x
    exact Submodule.Quotient.mk_eq_zero _

  rw [@locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, @locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, hlat, hlat]
  have hdual : ∀ M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E),
      LdG (I.rec7 l Z) i hi M = Formalism.HermitianLatticesTheory.dual (hStd (I.rec7 l Z).host.E ((I.rec7 l Z).R.N i)) M := fun M => by
    unfold LdG
    rw [hg1]
    unfold dualL
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ M
  have hok : (I.atIn u a).Ok := l.lev u a
  have hT := hok.tied i
  have hSok : (I.stp u a i).Ok := (l.ch u a).step i
  have hmul := mulLat_Lsh_rep (I.stp u a i) hSok c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) (congrArg Units.val hγ)
  have hm := moveHyp_of_ok l.pr u v
  have hMove : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hm.ne, hm.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hsep := sepElt_of_ok l.pr u
  have hOk := ok_dn_extF (hT.ok c.1.1 ((I.stp u a i).rep c.1)) v hMove (hT.dnN_eq c.1.1 ((I.stp u a i).rep c.1) v) g hg
  have key : Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal
      (Formalism.L2.Forms.mulLat γ.1.1 ((I.stp u a i).Lsh c.1.1
        ((I.stp u a i).rep ((I.stp u a i).cl c.1.1 (((I.atIn u a).A i).dnPt v c.1 g))))) =
      Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (((I.atIn u a).A i).deco c.1.1 ((I.stp u a i).rep c.1)).L := by
    refine (congrArg (Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal)
      (hmul.trans ((hT.Lsh_eq _ _).trans (congrArg Deco.Lsh (hT.dn_deco _ _ _ _ hOk))))).trans ?_
    exact locP_Lsh_dn hsep (hT.ok _ _) v hMove.ne hOk
  exact (congrArg (fun M => Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (Formalism.L2.Forms.mulLat γ.1.1 M))
    (hdual _)).trans key
end

