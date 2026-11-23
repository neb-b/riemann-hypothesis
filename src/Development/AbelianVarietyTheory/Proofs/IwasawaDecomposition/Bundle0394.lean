module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0363
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowLower
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagLiftTranslationMemTypeLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaChart

theorem normal_rep {G D A : Type} [Group G] [MulAction G D] (f : D → A) (pref : D → Prop)
    (h : ∀ q, pref q ↔ f q = Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩))
    (d d' : D) (hd : ∀ g : G, f (g • d') = f (g • d)) :
    f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) d')) = f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) d)) := by
  have h1 : ∀ (q : D) (g₀ : G), (fun r => ∃ g : G, r = f (g • g₀ • q)) = fun r => ∃ g : G, r = f (g • q) := fun q g₀ => by
    funext r
    refine propext ⟨fun ⟨g, e⟩ => ⟨g * g₀, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * g₀⁻¹, by
      rw [mul_smul, inv_smul_smul]; exact e⟩⟩
  have h2 : ∀ q : D, f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) q)) =
      Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩) := fun q => by
    have hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk (MulAction.orbitRel G D) q ∧ pref p := by
      obtain ⟨g, hg⟩ := Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩
      refine ⟨g • q, Quotient.sound ⟨g, rfl⟩, (h _).2 ?_⟩
      rw [h1]
      exact hg.symm
    unfold prefRep
    rw [dif_pos hex]
    obtain ⟨g, hg⟩ : ∃ g : G, g • q = hex.choose := Quotient.exact hex.choose_spec.1
    have h3 := (h _).1 hex.choose_spec.2
    rw [h3, ← hg, h1]
  rw [h2, h2]
  simp only [hd]

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem mv_dia (q : PtAt R sel mu cst u j) (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    PtY.mv q (DecoSet.dia1 P a q.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a q.1.1.deco, q.1.1.1.2), q.1.1.2⟩, q.1.2), q.2⟩ := by
  unfold PtY.mv
  exact dite_eq_left ⟨q.1.1.2, q.2⟩

theorem cosetIn_dia (q : PtAt R sel mu cst u j) (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    cosetIn (PtY.mv q (DecoSet.dia1 P a q.1.1.deco) : PtAt R sel mu cst u j) = cosetIn q := by
  rw [mv_dia]
  rfl

theorem cosetIn_of_ne (h : j + 1 ≠ R.m) (q : PtAt R sel mu cst u j) : cosetIn q = fun _ => ∅ := by
  have h2 : q.1.2 = ∅ := by
    have := q.2
    rw [ysAt_ys_of_ne sel mu cst h] at this
    exact this
  funext P
  unfold cosetIn
  rw [h2]
  simp

end Pt

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev dp (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl) :
    (I.stp u a i).D c.1 := PtY.mv ((I.stp u a i).rep c) (DecoSet.dia1 P s ((I.stp u a i).rep c).1.1.deco)

theorem cosetIn_rep (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ)
    (c : (I.stp u a i).Cl) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c))) = cosetIn ((I.stp u a i).rep c) := by
  by_cases h : i + 1 = B.R.m
  · have h2 := @normal_rep ((I.stp0 u a i).G c.1) ((I.stp0 u a i).D c.1) _ _ ((I.stp0 u a i).actD c.1) (fun q => cosetIn q) (I.pref u a i c.1)
      (fun q => ⟨fun hq => hq.2.1 h, fun hq => ⟨fun h0 => by have := B.R.two_le_m; omega, fun _ => hq, fun h0 => by omega⟩⟩)
      ((I.stp u a i).rep c) (dp I u a i P s c) (fun g => by
        have e := ((l.lev u a).lev i).dia_act c.1 P s g ((I.stp u a i).rep c)
        exact (congrArg (fun q : (I.stp0 u a i).D c.1 => cosetIn q) e.symm).trans (cosetIn_dia _ P s))
    refine h2.trans ?_
    exact congrArg (fun q => cosetIn ((I.stp u a i).rp c.1 q)) ((I.stp u a i).rp_spec c.1 c.2)
  · rw [cosetIn_of_ne h, cosetIn_of_ne h]


set_option maxHeartbeats 1000000 in
theorem exists_level (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl)
    (δ : GA B (B.R.N i)) (hδ : PtOf (y c * δ * k (chOf c)) (dp I u a i P s c).1.1) (β : Ch)
    (hβ : chOf ((I.stp u a i).cl c.1 (dp I u a i P s c)) = β) :
    ∃ x : U β, y c * δ = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a i).gam c.1 ((I.stp u a i).mv c.1 (dp I u a i P s c))) * y ((I.stp u a i).cl c.1 (dp I u a i P s c)) * x.1 ∧
      ((chi β x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 ((I.stp u a i).mv c.1 (dp I u a i P s c)) : B.LLˣ) : B.LL) := by
  subst hβ
  have hch : chOf ((I.stp u a i).cl c.1 (dp I u a i P s c)) = chOf c := (h.key _ _).2 ⟨rfl, cosetIn_rep I l u a i P s c⟩
  have hg := (I.stp u a i).mv_smul c.1 (dp I u a i P s c)
  have hco := cosetIn_rep I l u a i P s c
  have hco' : cosetIn (dp I u a i P s c) = cosetIn ((I.stp u a i).rep c) := cosetIn_dia _ P s
  generalize (I.stp u a i).mv c.1 (dp I u a i P s c) = g at hg ⊢
  rw [← hch] at hδ
  have hlev := h.lev ((I.stp u a i).cl c.1 (dp I u a i P s c))
  have hchr := h.chr ((I.stp u a i).cl c.1 (dp I u a i P s c))
  generalize y ((I.stp u a i).cl c.1 (dp I u a i P s c)) = y' at hlev hchr ⊢
  obtain ⟨γ, κ⟩ := g
  have hk : (I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c))) =
      (I.stp u a i).act c.1 (γ⁻¹, 1) (dp I u a i P s c) := by
    refine Eq.trans ?_ (congrArg ((I.stp u a i).act c.1 (γ⁻¹, 1)) hg)
    refine Eq.trans ?_ (((I.stp u a i).actD c.1).mul_smul (γ⁻¹, 1) (γ, κ) _)
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    rfl
  have hpt : PtOf (y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ))) * k (chOf ((I.stp u a i).cl c.1 (dp I u a i P s c))))
      ((I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c)))).1.1 := by
    rw [hk, mul_inv_cancel_left, mul_assoc]
    exact GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ _ _ _ _ _ γ⁻¹ _ _ hδ
  have hx := (hlev _ _ hpt).2 ⟨(1, κ), map_one (ufGL _ _), rfl, by
    refine Eq.trans ?_ (hco'.trans hco.symm)
    refine (congrArg (fun q : (I.stp u a i).D c.1 => cosetIn q) hk).trans ?_
    exact GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ⁻¹ rfl rfl⟩
  refine ⟨⟨_, hx⟩, ?_, hchr ⟨_, hx⟩ (1, κ) (map_one (ufGL _ _)) hpt⟩
  show y c * δ = ratAd B.host.F γ * y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ)))
  rw [mul_assoc, mul_inv_cancel_left, ← mul_assoc]
  unfold ratAd
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]


set_option maxHeartbeats 1000000 in
theorem isPt_dia (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl)
    {f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J (B.T u) f bad) (hL : S.Lb = Lb (chOf c))
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : (B.T u : 𝓞 B.host.F) ∈ v.asIdeal) (hP : v = P.1.under (𝓞 B.host.F))
    (hs : ∀ t t' : latS (F := B.host.F) (v.adicCompletion B.host.F) (intV B.host.E v)
        (Submodule.span (𝓞 B.host.E) (dualSet (B.sp.cm.sig : B.host.E →+* B.host.E) J S.Lb)),
      t'.1 = inclE (F := B.host.F) (v.adicCompletion B.host.F) ((X.piT u : 𝓞 B.host.E) : B.host.E) • t.1 → S.fT v hv t' = 0)
    (z : ℤ) (hz : (z : 𝓞 B.fields.E ⧸ P.1.asIdeal) = s) (δ : UPts B.sp.cm.sig J (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
    (hδ : IsDia S v hv z δ) : PtOf (y c * δ.1 * k (chOf c)) (dp I u a i P s c).1.1 := by
  classical
  have hX := FieldsLaws.fields_ok B
  have hPr := l.pr
  have hover : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 := fun w hw =>
    (under_eq_iff B.host P.1 w).1 (hw.trans hP)
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.diamondElement_integral_support_lastRow _ _ B.sp.cm _ _ _ _ J S (X.piT u) P.1 v hv z δ hJ hP.symm hover
    (decoFin_mem_of_mem_divs P.2) (hPr.piT_notMem_sq hX u P.2) (conj_piT_notMem hPr u P)
    (fun x => by rw [hL]; exact h.lb _ x) hs hδ
  obtain ⟨p₀, hp₀, hN⟩ := h.k_std (chOf c)
  have hdis : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_left.2 fun w hw hw' => by
    obtain ⟨j, hj⟩ := exists_g_mem hPr ⟨w, hw⟩
    exact GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hw' (hPr.g_prime j) (hI.g_mem j) hj
  have hT : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → (B.T u : 𝓞 B.host.E) ∈ w.asIdeal := fun w hw => by
    rw [← hw] at hv
    have h1 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.asIdeal := hv
    rwa [map_natCast] at h1
  refine _root_.GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ B.sp.cm _ _ _ _ (y c) δ.1 (k (chOf c)) ((I.stp u a i).rep c).1.1 _ P s _
    ((h.pt c).of_extTo (I.Q_subset_SQ a) hdis) hp₀.uni (by subst hJ; exact δ.2) (hN ▸ hp₀.lat) d1 d2
    (fun w hw => d3 w fun e => ?_) (h.k_T _ P) (fun r j hr => hz ▸ d4 r j hr) ?_ ?_
  · rcases hw with hw | hw | ⟨hw, hne⟩
    · exact T_notMem_vGs hPr u ⟨w, hw⟩ (hT w e)
    · exact GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hw (hPr.T_prime u) (hI.T_mem u) (hT w e)
    · rcases hover w e with e' | e'
      · exact hne e'
      · refine conj_piT_notMem hPr u P ?_
        have h1 : X.piT u ∈ w.asIdeal := decoFin_mem_of_mem_divs hw
        rw [e'] at h1
        exact h1
  · exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u i => q.1.1.deco) (mv_dia _ P s)
  · exact (congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u i => q.1.1.fr) (mv_dia ((I.stp u a i).rep c) P s) :)


set_option maxHeartbeats 4000000 in
theorem dilTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}), I.ReadsK l Z u a i hi chOf K → (∀ β, FunKilled (K β).lev (X.piT u)) → I.IdY l Z u a i hi eY → I.IdV l u a eV → DilationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY eV chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  intro B X I hI hPins l Z u a i hi bad Ch chOf K eY eV hR hs hY hV
  obtain ⟨k, hR⟩ := hR
  have hJ := ((_root_.GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hPins l Z).2.2.2 i hi).1
  have hch : ∀ v s c, chOf ((I.fm l u a).dil i v s c) = chOf c := fun v s c =>
    (hR.key _ _).2 ⟨rfl, cosetIn_rep I l u a i v s c⟩
  have hy : ∀ β (c : {c // chOf c = β}), ((K β).y c).1 = ((K (chOf c.1)).y ⟨c.1, rfl⟩).1 := by
    rintro _ ⟨c, rfl⟩
    rfl
  have key : ∀ v (s : ((I.atT l u a).Fv v)ˣ) (z : ℤ), (z : (I.atT l u a).Fv v) = s → ∀ β (c : {c // chOf c = β}) δ,
      IsDia (K β).lev (eV v).1 (eV v).2 z δ → ∃ x : (K β).lev.U,
        ((K β).y c * δ).1 = bc (n := Fin ((I.rec7 l Z).R.N i)) (inclE (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
          (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))
          ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) *
            ((K β).y ⟨(I.fm l u a).dil i v s c.1, (hch v s c.1).trans c.2⟩).1 * x.1 ∧
        (((K β).lev.chi x : ℂˣ) : ℂ) =
          B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)) : B.LLˣ) : B.LL) := by
    rintro v s z hz _ ⟨c, rfl⟩ δ hδ
    have h1 := isPt_dia I hI l u a i hR v s c hJ (K (chOf c)).lev rfl (eV v).1 (eV v).2 (hV v) (hs _ _ _) z hz δ hδ
    obtain ⟨x, hx1, hx2⟩ := exists_level I l u a i hR v s c δ.1 h1 (chOf c) (hch v s c)
    refine ⟨x, ?_, hx2⟩
    rw [hy (chOf c) ⟨(I.fm l u a).dil i v s c, _⟩]
    exact hx1
  have hU : ∀ b (g : (I.stp u a i).G b), (I.stp u a i).gam b g ∈
      UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := fun b g => by
    rw [hJ]
    show cT _ _ * 1 * _ = 1
    rw [mul_one]
    exact ((l.ch u a).step i).unit b g
  refine ⟨hch, fun v s z hz β c δ hδ => ?_, fun v s z hz β c δ hδ g hg => ?_⟩
  · obtain ⟨x, hx, -⟩ := key v s z hz β c δ hδ
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ?_
    have hγ := hU c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))
    have hxU := (((K β).lev.U_eq x.1).1 x.2).1
    have hγ' : bc (n := Fin ((I.rec7 l Z).R.N i)) (inclE (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
        (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))
        ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) ∈
          UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
      have := mul_mem (mul_mem ((K β).y c * δ).2 (inv_mem hxU))
        (inv_mem ((K β).y ⟨(I.fm l u a).dil i v s c.1, (hch v s c.1).trans c.2⟩).2)
      rwa [hx, mul_inv_cancel_right, mul_inv_cancel_right] at this
    exact ⟨⟨_, hγ'⟩, ⟨_, hγ, rfl⟩, ⟨x.1, hxU⟩, x.2, Subtype.ext hx⟩
  · obtain ⟨x, hx, hc⟩ := key v s z hz β c δ hδ
    funext t
    have h1 := hg _ (hU c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) _ ((K β).y c * δ) x hx (eY t)
      (eY (frMul B.fields.emb B.embLL ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)))⁻¹ t)) (fun τ => by
        rw [hY, hY]
        have e := congrArg (fun q => q.1 τ) ((frEquiv B.fields.emb B.embLL
          ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)))).apply_symm_apply t)
        refine e.symm.trans ?_
        have e2 : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := FieldsLaws.embLL_comp_emb B τ
        unfold Formalism.L2.Forms.atInf
        rw [← e2]
        rfl)
    rw [h1, hc]
    rfl

end GlobalTheory.Mem.Col2.DiaChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Grp

theorem coeff_conj_of_central {G : Type} [Group G] (e : MonoidAlgebra ℂ G) (he : ∀ x, x * e = e * x) (k g : G) :
    e.coeff (k * g * k⁻¹) = e.coeff g := by
  have h := congrArg (fun a : MonoidAlgebra ℂ G => a.coeff (k * g)) (he (MonoidAlgebra.single k 1))
  simp only [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply] at h
  simpa [mul_assoc] using h.symm

theorem idemOf_coeff_conj : ∀ (X : Stages) (px : PreX X.B.toPre) (eR : Gc X.B px ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), GoodSet X (px := px) eR Xg → X.toD7.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g X.toD7.nd)) → ∀ a b : Gc X.B px, (idemOf Xg).coeff (a * b * a⁻¹) = (idemOf Xg).coeff b := by
  intro X px eR Xg hgood hc a b
  apply X.B.embLL.injective
  rw [hgood.2, hgood.2, map_mul eR, map_mul eR, map_inv eR]
  exact coeff_conj_of_central _ (Subalgebra.mem_center_iff.1 hc) _ _

theorem grp_levels_exist : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → GrpAt X I → LevOf X I U L → ∃ (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r) (cG : G0 L.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (Xg : Finset (Gc X.B px → X.B.LL)), IsPlacewiseIdentity X (px := px) eG ∧ GoodSet X (px := px) (eG.trans cG) Xg ∧ PsiPPTie X.toD7 (lev0 I) (chr0 I) (lev1 I) (chr1 I) (eG.trans cG) ∧ (∀ g, (idemOf Xg).coeff g ∈ X.B.Ks) ∧ (∀ p, ((chr0 I p : X.B.LLˣ) : X.B.LL) ∈ X.B.Ks) ∧ ∀ tr, IdemClass (D := X.toD7) (famR X I hX U Xg tr).A ∧ Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 ∧ ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ L.Pg) (iso : ∀ kv : (Σ k : Fin 2, X.toD7.nd.PlG k), ZMod (X.toD7.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : L.Pg) : Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv) := by
  intro X px I hX U L hI hG hL
  obtain ⟨eG, cG, plg, iso, hid, hpl, hdiv, hbc⟩ := GlobalTheory.T.exists_finiteGroupIdentification_fixedPlaces X px I U L hI hG hL
  obtain ⟨Xg, hgood, hKs⟩ := GlobalTheory.T.exists_goodCharacterSet_idempotent_coeff_coefficientField X px (eG.trans cG)
  refine ⟨eG, cG, Xg, hid, hgood, GlobalTheory.T.psiLevelPairCompatible_of_columnLevels X px I U L eG cG plg iso hI hL hid hpl hbc, hKs, _root_.GlobalTheory.Mem.R3.chr0_mem_Ks X.B px I,
    fun tr => ⟨?_, GlobalTheory.T.columnFaceLevels_baseLevel_symmetricLevel X px I hX U Xg tr L eG hI hL hid, plg, iso, hpl, hdiv, hbc⟩⟩
  exact idemOf_coeff_conj X px (eG.trans cG) Xg hgood hG.cen

end GlobalTheory.Mem.R3.Grp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayeredDataOfGoodScaleContexts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem recExP_of_recAtG : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  intro hconds Q' QO h hq
  obtain ⟨ε0, hε0, h⟩ := h
  obtain ⟨ε1, hε1, hq⟩ := hq
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun eps C8 C5 c6 Cb he he0 he52 hC8 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb he (he0.trans (min_le_left _ _)) he52 hC8
  obtain ⟨K1, hq⟩ := hq eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he52 hC8
  refine ⟨K0.sup K1, fun C hstd hC hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hstd hC (large_of_sup hL).1
  obtain ⟨c1', hq⟩ := hq C hstd hC (large_of_sup hL).2
  refine ⟨max (max c1 c1') 0, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2q, hq⟩ := hq cD (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcD)
  obtain ⟨c2', hlow⟩ := GlobalTheory.EX.WinLow.window_lower hconds eps C he he52 hstd cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max (max c2 c2q) c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hch)
  have hq := hq ch (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hch)
  obtain ⟨x1, hlow⟩ := hlow ch (le_trans (le_max_right _ _) hch)
  obtain ⟨x2, hint⟩ := exists_du_nat eps he he52
  have hq' : ∃ x3 : ℝ, Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩ → ∀ K : Ctx, Par.Of ⟨eps, C, cD, ch, C5, c6, Cb⟩ K → x3 ≤ K.s.x →
      ∀ β : BPt K, β.Is Q' → QO ⟨eps, C, cD, ch, C5, c6, Cb⟩ β.D β.O := by
    by_cases hp : Par.Pos ⟨eps, C, cD, ch, C5, c6, Cb⟩
    · obtain ⟨x3, h3⟩ := hq hp
      exact ⟨x3, fun _ => h3⟩
    · exact ⟨0, fun hp' => absurd hp' hp⟩
  obtain ⟨x3, hq'⟩ := hq'
  refine ⟨1, max (max x0 x3) (max x1 x2), one_pos, fun s P a b c hs hx d3 => ?_⟩
  have hok := d3.ok
  have hx0 : x0 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨du, hpos, hdu⟩ := hint s C cD ch P _ a b c hs hx2 hok
  obtain ⟨hD, hDle⟩ := GlobalTheory.Mem.Top.DsLow.DsP_pos_and_lower P
  refine ⟨du, DsP P, hpos, hD, fun u => ?_, fun Lv h1 h2 h3 => ?_⟩
  · rw [one_mul]
    exact hlow s P _ a b c du (DsP P) hs hx1 hok hdu hDle u
  · let K : Ctx := ⟨s, C, cD, ch, P, _, a, b, c, hstd, hok, Lv, fun u => by rw [h1]; exact hdu u, h2, h3⟩
    obtain ⟨D, Y, g1, g2, g3, g4, ⟨X, f, T, co, hQ, he⟩, u1, u2, u3⟩ := h K rfl rfl rfl hs hx0 d3
    refine ⟨D, Y, g1, g2, g3, g4, fun p p1 p2 p3 p4 => ⟨fun hp => ?_, ?_⟩⟩
    · obtain ⟨rfl, he⟩ := Sigma.mk.inj he
      exact hq' hp K ⟨rfl, rfl, rfl, hs, d3⟩ hx3
        ⟨X, f, T, co, Y, eq_of_heq he, p, p1, p2, p3, p4, ⟨C5, c6, Cb, d3⟩, g2, g3, u1, u2⟩ hQ
    · exact DQ.qd_setDiv D (Y.obj p) (nPrime p.L) p.ht ⟨u1, u2, u3⟩

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPtOfMulK1Standard
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh.KStd

theorem K1_le_J0_empty {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) :
    K1 B.sp.cm n ST SG ≤ J0 B.sp.cm n ∅ := by
  intro t ht
  have h1 := principal_le_congruence_subgroup B.sp.cm n ST SG ht
  unfold J0 at h1 ⊢
  simp only [Subgroup.mem_inf] at h1 ⊢
  refine ⟨h1.1, ?_⟩
  simp

theorem exists_ptOf_mul_K1 : ∀ {B : Base} (n : ℕ) [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 B.host.E))) (k t : GA B n), t ∈ K1 B.sp.cm n ST SG → (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) → ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E n := by
  intro B n _ ST SG k t ht ⟨p, hp, hN⟩
  have hz : t ∈ J0 B.sp.cm n ∅ := K1_le_J0_empty n ST SG ht
  refine ⟨p, ?_, hN⟩
  refine (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw B.host.F B.host.E B.sp.cm n ∅ ∅ ∅ (k * t) p rfl).2 ⟨?_, ?_⟩
  · exact mul_mem hp.uni (congruence_le_adelic_unitary B.sp.cm n ∅ hz)
  · have h := decoRaw_rawSm B.sp.cm ∅ ∅ 1 (⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) k
    rw [map_one, map_inv] at h
    have e : Formalism.UG.bc (iA B.host.F B.host.E) ((1 : URat B.sp.cm n) : GL (Fin n) B.host.E) * k *
        (((⟨t, hz⟩⁻¹ : J0 B.sp.cm n ∅) : J0 B.sp.cm n ∅) : GL (Fin n) (AfE B.host.F B.host.E))⁻¹ = k * t := by
      simp
    rw [e] at h
    have hr : (redG B.sp.cm n ∅ ∅ ⟨t, hz⟩)⁻¹ = 1 := Subsingleton.elim _ _
    rw [hr] at h
    rw [(near_of_isPtOf hp 0).deco] at h
    simp only [map_one] at h
    change decoRaw ∅ ∅ (k * t) = Deco.act 1 1 p.deco.1 at h
    rw [Deco.act_one] at h
    exact h.symm

end GlobalTheory.Mem.Col2.TopCh.KStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagLiftTranslationMemTypeLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLift_translation_mem_typeLevel_character : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ hh : (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹ *
          Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ) ∈
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
        X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨_, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
          (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.inv_redZ_mul_g0Hat_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → ∀ σ ∈ Ine (F := E) A, σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A := by
  first | exact @GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | exact GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine | (intros; apply GlobalTheory.InertiaTwoPlaces.eq_of_mem_Ine_of_mem_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0DecorationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPtOf_mul_J0_decoration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g z : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q) (h : GLG (E := E) (n := n) (SG := SG)), (IsPtOf hc g p → IsPtOf hc (g * z) p' → ((∃ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹) ↔ p'.deco = ((1, h) : UF E n × GLG (E := E) (n := n) (SG := SG)) • p.deco)) ∧ (Q = ∅ → IsPtOf hc g p → ∀ hz : z ∈ J0 hc n ST, redG hc n ST SG ⟨z, hz⟩ = h⁻¹ → IsPtOf hc (g * z) (((1, h, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) ∧ (Q = ∅ → g ∈ UAd hc n → ∃ q : DecoF E n ST SG Q, IsPtOf hc g q) := by
  exact @GlobalTheory.Mem.Col2.TopCh.isPtOf_mul_J0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTupleGroupClassesCoordinatesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_tuple_group_classes_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  exact GlobalTheory.stpTop_groupClasses I u a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecoratedStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointLattice_iff_baseLattice_decorated : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  first | exact @GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | exact GlobalTheory.Mem.Col2.PtLat.latS_deco_iff | (intros; apply GlobalTheory.Mem.Col2.PtLat.latS_deco_iff <;> assumption)
end

