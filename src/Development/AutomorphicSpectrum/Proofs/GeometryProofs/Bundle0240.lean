module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartAdic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0238
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem pull_eq {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X)
    {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (j : E →+ F)
    (p' : Cpt ξ') (hq : genPt ξ ⤳ f p'.1) :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, hq⟩ : Set E)) := by
  unfold Lat.pull
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨hq, e, he, rfl⟩

theorem unitAt_natCast {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    simpa [unitAt] using (regAt ξ q).one_mem
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun e => hn (by simp [e])
    have hb0 : b ≠ 0 := fun e => hn (by simp [e])
    obtain ⟨a1, a2, a3⟩ := ha ha0 fun p hp hd => h p hp (hd.mul_right _)
    obtain ⟨b1, b2, b3⟩ := hb hb0 fun p hp hd => h p hp (hd.mul_left _)
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.cast_mul]; exact mul_ne_zero a1 b1
    · rw [Nat.cast_mul]; exact (regAt ξ q).mul_mem a2 b2
    · rw [Nat.cast_mul, mul_inv]; exact (regAt ξ q).mul_mem a3 b3

theorem noeth_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hg : IsCptGen ξ) (q : Cpt ξ)
    (h : IsNoetherianRing (regAt ξ q)) : IsNoetherianRing (X.presheaf.stalk q.1) :=
  isNoetherianRing_of_ringEquiv (regAt ξ q) (RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun a b e => hg.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩).symm

set_option maxHeartbeats 1000000 in
theorem hodgeCpt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A x Z ξ' h hx hS hvb hall htie hnorm hdom
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hgen := A.tie.gen
  have hgen' := htie.gen
  obtain ⟨t', ⟨mh⟩⟩ : ∃ t' : SAB H Z, Nonempty (SABMap t' A.t h) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM Out.proved_CubePullSt h A.t⟩⟩
  obtain ⟨mf, hmf⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ A.m mh
  obtain ⟨Li', acg', mod', ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Z t'.G Ω' ξ'
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act Z t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieJ.exists_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' hdom mh.cart
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LiePull.main A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseAct.baseChange_act A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j (𝓞 E) A.t.act.act t'.act.act A.ρ ρ'
    hdom mh.cart hj A.act hρ' (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.DualExt.dual_ext Ω Ω' i A.Li Li' j hext hspan
  have hW : ∀ s, eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    _root_.GlobalTheory.CompanionTheory.Ar.EigExt.eigSp_ext E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ Z Ω' ξ' h i hdom
  have hsp : ∀ p' : Cpt ξ', genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt ξ' p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt ξ' p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt ξ'), InFibre ξ' p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian Z Ω' ξ' ℤ _ _ htie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => (A.normal q.1).2
  have hic' : ∀ q : Cpt ξ', IsIntegrallyClosed (Z.presheaf.stalk q.1) := fun q => (hnorm q.1).2
  have htors : ∀ p ∈ S, FullTorsion t'.G ξ' (p ^ A.R p) := fun p hp =>
    _root_.GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    _root_.GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt ξ', 0 < D.p + D.q → M'.htOm t'.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt ξ' p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at E H D l Xo c O β Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at E H D l Xo c O β Y Z (h ≫ A.f) t' mf Ω' ξ' (spMap i ≫ x) (by
      rw [← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.OmLink.htOm_eq_htLat E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := _root_.GlobalTheory.CompanionTheory.Ar.OmLink.htOm_eq_htLat E H D l (KA l) (baseKA l) Z Ω' ξ' s0' o' t' m0' Li' M' (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := _root_.GlobalTheory.CompanionTheory.Ar.HTPull.main A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq ξ' h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt ξ' p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    have hq := (hfib p p').1 hf
    obtain ⟨U, hU, b, hb, hfr⟩ := hvb p hp s ⟨h p'.1, hsp p'⟩ hq
    obtain ⟨hli, hbs⟩ := hfr ⟨h p'.1, hsp p'⟩ hq hU
    exact _root_.GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j jd (A.Vgen s) _
      (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩) (M'.htOm t'.PP.L (p ^ A.R p) p') (labelRk D s) b hext (hreg p') hjd
      (hW s) (fun hr => hω p hp p' (hpos s hr)) hli hb hbs
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htW t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt ξ' p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.differentIdeal_principal_in_localSubring E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact _root_.GlobalTheory.CompanionTheory.Ar.scale_pull_ext Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p' hf)
  have hV : ∀ s, Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull ξ' h j := by
    intro s
    funext p'
    rw [pull_eq ξ' h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre ξ' p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p' hf
      · exact hdual p hp _ p' hf
    · have hc' : ∀ p ∈ S, ¬ InFibre ξ' p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      have hdisc : (((NumberField.discr E : ℤ) : Ω))⁻¹ ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := by
        have hn0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
        obtain ⟨-, -, hu⟩ := unitAt_natCast (ξ := A.ξ) ⟨h p'.1, hsp p'⟩ _ hn0 fun p hpp hd => by
          have hin := hS p hpp (Int.natCast_dvd.2 hd)
          exact not_not.1 (hc'' p hin)
        rcases Int.natAbs_eq (NumberField.discr E) with e | e
        · rw [e]; simpa using hu
        · rw [e]
          simpa using (regAt A.ξ ⟨h p'.1, hsp p'⟩).neg_mem hu
      show M'.lat p' ⊓ _ = _
      rw [hlat, pull_eq ξ' h _ j p' (hsp p')]
      exact _root_.GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) _ _ (A.M.lat ⟨h p'.1, hsp p'⟩) hext hρj (hreg p')
        (fun a e he => _root_.GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) (hint s _) hdisc
  have hvb' : ∀ s, (Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s)).IsVB (labelRk D s)
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))) := by
    intro s
    rw [hV s, hW s]
    have h3 := _root_.GlobalTheory.CompanionTheory.Ar.LatPull.isVBOn_pull A.X Ω A.ξ A.Li Z Ω' ξ' h i Li' j (A.V s) Set.univ (labelRk D s) (A.Vgen s) hdom hext.1 hext.2
      (A.vb s)
    intro p' _
    obtain ⟨U, hU, b, hb, hfr⟩ := h3 p' ⟨hsp p', trivial⟩
    exact ⟨U, hU, b, hb, fun q _ hq => hfr q ⟨hsp q, trivial⟩ hq⟩
  have hvbt : ∀ p ∈ S, ∀ s, ((M'.htOm t'.PP.L (p ^ A.R p)).map
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))).dualRestrict).IsVBOn {q | InFibre ξ' p q} (labelRk D s) ⊤ := by
    intro p hp s
    exact _root_.GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull A.X Z Ω Ω' A.ξ ξ' h i A.Li Li' j jd (A.Vgen s) _ (A.M.htOm A.t.PP.L (p ^ A.R p))
      (M'.htOm t'.PP.L (p ^ A.R p)) {q | InFibre A.ξ p q} {q | InFibre ξ' p q} (labelRk D s) hdom hgen' hext hjd (hW s)
      (hvb p hp s) fun p' hf => ⟨hsp p', (hfib p p').1 hf, fun hr => hω p hp p' (hpos s hr)⟩
  let m' : SABMap t' A.t ((Iso.refl Z).hom ≫ h) :=
    { cm := mh.cm
      cart := by simpa using mh.cart
      base := by simpa using mh.base
      act := mh.act
      lin := mh.lin }
  refine ⟨{ X := Z, ξ := ξ', all := hall, tie := htie, normal := hnorm, f := h ≫ A.f, Ω₀ := A.Ω₀, ξ₀ := A.ξ₀,
            gen₀ := A.gen₀, cst := i.comp A.cst, cst_over := ?_, fn := i.comp A.fn, fn_over := ?_, t := t', m := mf,
            Li := Li', M := M', ρ := ρ', act := hρ', S_prime := A.S_prime, R := A.R, R_ge := A.R_ge, tors := htors,
            vb := hvb' }, Iso.refl Z, j, m', ?_, ?_, ?_, rfl, rfl, hext, hj, hvbt, ?_⟩
  · have e : ξ' ≫ h = spMap i ≫ A.ξ := hdom
    have e2 : ξ' ≫ h ≫ A.f ≫ Y.s = spMap i ≫ A.ξ ≫ A.f ≫ Y.s := by
      rw [← Category.assoc, e, Category.assoc]
    simp only [Category.assoc]
    rw [e2, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← Category.assoc, hdom, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp
  · simp
  · exact hmf
  · intro s
    have e : (Iso.refl Z).hom ≫ h = h := Category.id_comp h
    refine (hV s).trans ?_
    exact congrArg (fun g => (A.V s).pull ξ' g j) e.symm

end GlobalTheory.CompanionTheory.Ar.HcptPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartIntegral
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.TestPts

theorem isProper_snd_comp {G S Y Z : Scheme.{0}} (f : G ⟶ S) (h : Y ⟶ S) (g : Z ⟶ Y)
    [IsProper (Limits.pullback.snd f h)] : IsProper (Limits.pullback.snd f (g ≫ h)) := by
  have hc : Limits.pullback.fst f (g ≫ h) ≫ f = (Limits.pullback.snd f (g ≫ h) ≫ g) ≫ h := by
    rw [Limits.pullback.condition, Category.assoc]
  have hp : IsPullback (Limits.pullback.lift _ _ hc) (Limits.pullback.snd f (g ≫ h))
      (Limits.pullback.snd f h) g := by
    refine IsPullback.of_right (h₁₂ := Limits.pullback.fst f h) (v₁₃ := f) (h₂₂ := h) ?_
      (Limits.pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback f h)
    rw [Limits.pullback.lift_fst]
    exact IsPullback.of_hasPullback f (g ≫ h)
  exact MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance

theorem exists_unit_of_pow {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    (u : (FractionRing O)ˣ) (m : ℕ) (hm : 0 < m) (h : u ^ m = 1) :
    ∃ w : Oˣ, algebraMap O (FractionRing O) w = u := by
  have h1 : IsIntegral O (u : FractionRing O) :=
    IsIntegral.of_pow hm (by rw [← Units.val_pow_eq_pow_val, h]; exact isIntegral_one)
  have h2 : IsIntegral O ((u⁻¹ : (FractionRing O)ˣ) : FractionRing O) :=
    IsIntegral.of_pow hm (by rw [← Units.val_pow_eq_pow_val, inv_pow, h]; simpa using isIntegral_one)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_one]; simp
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

theorem finite_levGrp (La : Type) [AddCommGroup La] [Module.Finite ℤ La] (p n : ℕ) (hp : 0 < p) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) x
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change ((p ^ n : ℕ) : ℤ) • (Submodule.Quotient.mk a : La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  exact this

theorem finrank_eq_rankAtStalk {A Q : Type} [CommRing A] [IsDomain A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Projective A Q] (P : PrimeSpectrum A) :
    Module.finrank A Q = Module.rankAtStalk Q P := by
  have hbc := TensorProduct.isBaseChange A Q (FractionRing A)
  haveI := Module.finitePresentation_of_projective A Q
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing _ hbc,
    LieRank.finrank_of_isBaseChange _ hbc (IsLocalRing.closedPoint (FractionRing A))]
  exact (Module.isLocallyConstant_rankAtStalk (R := A) (M := Q)).apply_eq_of_preconnectedSpace _ _

theorem finrank_lie_eq (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom]
    (R O : Type) [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] [Algebra R O]
    (x : Sp R ⟶ S) (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module O L']
    (M : LieModel G x L) (M' : LieModel G (spMap (algebraMap R O) ≫ x) L') :
    Module.finrank O L' = Module.finrank R L := by
  obtain ⟨hf, hp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective S G R x L M
  letI : Module R L' := Module.compHom L' (algebraMap R O)
  haveI : IsScalarTower R O L' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G x M M'
  have hbc := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange S G R O x L L' M M' j hj
  rw [← LinearEquiv.finrank_eq hbc.equiv,
    finrank_eq_rankAtStalk (IsLocalRing.closedPoint (FractionRing O) |> PrimeSpectrum.comap (algebraMap O (FractionRing O))),
    Module.rankAtStalk_baseChange]
  exact (finrank_eq_rankAtStalk _).symm

theorem reduces_at_point (hPt : PointHT) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω]
    [Module R Ω] [IsScalarTower R K Ω]
    (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La)
    (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S]
    (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left)
    (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L)
    (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω)
    (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R)
    (hc : IsHTChartOf Dc Γ₀ i M ρ j π ζ₀)
    (hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k))
    (he : ∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n)))
    (hrank : 2 * Module.finrank R L = Module.finrank ℤ D.La)
    (hprop : IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)))
    (hκ : if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1)
    (C O : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsDomain O] [Algebra O C] [Algebra R O]
    (v : Valuation C NNReal) (hv : v.Integers O) (hp : v (p : C) < 1)
    (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (hinj : Function.Injective (algebraMap R O))
    [IsAlgClosed (FractionRing O)] [IsIntegrallyClosed O]
    (f : FractionRing R →+* FractionRing O)
    (hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r))
    (z : Sp (FractionRing O) ⟶ S) (hz : z = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x)
    (I : TateIso D (FractionRing O) (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))
    (hI1 : (I.ζ (p ^ n) : FractionRing O) = f (algebraMap R _ (ζ₀ : R)))
    (hI2 : ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) :
    ∃ (L' : Type) (_ : AddCommGroup L') (_ : Module O L')
      (P : HTPoint C O (IsCMField.complexConj E).toRingEquiv (algebraMap R O κ) (D.p + D.q) (C ⊗[ℤ] D.La)
        (C ⊗[O] Module.Dual O L'))
      (io : Dc.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L')), Dc.ReducesTo (algebraMap R O) P io := by
  subst hz
  have hppos : ∀ m, 0 < p ^ m := fun m => pow_pos (Fact.out : p.Prime).pos m
  haveI : CharZero O := charZero_of_injective_ringHom hinj
  obtain ⟨X, hX, hXi⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.tower_exists E H D S t p O _ I
  have hroot : ∀ m, ∃ w : Oˣ, algebraMap O (FractionRing O) w = (I.ζ (p ^ m) : (FractionRing O)ˣ) := fun m =>
    exists_unit_of_pow _ (p ^ m) (hppos m) (I.ζ_prim _ (hppos m)).pow_eq_one
  choose ζ hζ using hroot
  have hkinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hUinj : Function.Injective (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O)) :=
    Units.map_injective hkinj
  have hU : ∀ m, Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ m) = I.ζ (p ^ m) :=
    fun m => Units.ext (hζ m)
  have hprim : ∀ m, IsPrimitiveRoot (ζ m) (p ^ m) := fun m =>
    IsPrimitiveRoot.of_map_of_injective (f := Units.map (algebraMap O (FractionRing O) : O →* FractionRing O))
      (by rw [hU]; exact I.ζ_prim _ (hppos m)) hUinj
  have hcompat : ∀ m, ζ (m + 1) ^ p = ζ m := fun m => by
    apply hUinj
    rw [map_pow, hU, hU, pow_succ]
    exact I.ζ_pow _ _ (hppos m) (Fact.out : p.Prime).pos
  have hsq : (BT.genPt O).hom ≫ spMap (algebraMap R O) = spMap f ≫ (BT.genPt R).hom := by
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (hf r).symm
  have hprop' : IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x)) := by
    rw [← Category.assoc, hsq, Category.assoc]
    exact isProper_snd_comp _ _ _
  have hreg : X.PairingRegular D.EF ζ := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.HT.weil_regular E H S t p O _ D.La X D.EF ζ hprop' ?_
    intro m a b ga gb hga hgb
    have e1 : ga = I.ev (p ^ m) a := Over.OverMorphism.ext (hga.trans (hX m a))
    have e2 : gb = I.ev (p ^ m) b := Over.OverMorphism.ext (hgb.trans (hX m b))
    rw [e1, e2, map_zpow, hU]
    exact I.isom (p ^ m) (hppos m) a b
  haveI : Module.Finite ℤ D.La := hu.finite
  haveI := finite_levGrp D.La p n (Fact.out : p.Prime).pos
  have hSep : IsSeparated t.G.hom := t.semi.separated
  obtain ⟨F, hF1, hF2⟩ := _root_.PositivityTheory.HtPt.Htat.torsion_bc R (LevGrp D.La p n) Γ₀ S t.G x (p ^ n) i hi hSep O (algebraMap R O)
    (X.Γ n) (X.i n) (X.tors n) (FractionRing R) (algebraMap R _) (RingHom.id _) f
    (fun s => (Γ₀.pt s).left ≫ i) Function.injective_id (RingHom.id_comp _) (RingHom.ext hf)
    (fun s => by
      rw [Category.assoc, hi.isOver, ← Category.assoc, Over.w (Γ₀.pt s)]; rfl)
    (fun s => by simp)
    (fun s => by
      obtain ⟨q, rfl⟩ := Multiplicative.ofAdd.surjective s
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range ((p ^ n) • (LinearMap.id : D.La →ₗ[ℤ] D.La))) q
      change _ = ((X.Γ n).pt (lev p n a)).left ≫ X.i n
      rw [hX n a, hI2 a]; rfl)
  obtain ⟨L', iA, iM, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists S t.G O (spMap (algebraMap R O) ≫ x)
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act S t.G O (spMap (algebraMap R O) ≫ x) L' M' (𝓞 E)
    t.act.act t.act.hom t.act.one t.act.mul t.act.add
  haveI hsm : Smooth t.G.hom := t.semi.smooth
  have hrank' : 2 * Module.finrank O L' = Module.finrank ℤ D.La := by
    rw [finrank_lie_eq S t.G R O x L L' M M']; exact hrank
  obtain ⟨hκ1, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp C v O hv p R (algebraMap R O) κ hp hκ
  obtain ⟨P, hP⟩ := hPt p C v O hv hp hO E (IsCMField.complexConj E).toRingEquiv
    (fun a => IsCMField.complexConj_apply_apply E a) S t.G t.semi _ D.La D.EF (D.p + D.q) u hu X L' M' t.act.act ρ'
    t.act.hom hρ' hXi hrank' ζ hprim hcompat hreg (algebraMap R O κ) hκ1
  have hζ₀ : algebraMap R O (ζ₀ : R) = (ζ n : O) := by
    apply hkinj
    rw [← hf, ← hI1, hζ n]
  obtain ⟨io, hio⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.ChartRed.reducesTo_of_isHTChartOf p C v O hv hp hO E (IsCMField.complexConj E).toRingEquiv R K n (D.p + D.q) Ω Dc
    D.La D.EF u hu S t.G hsm x Γ₀ i hi L M t.act.act ρ hρ j hj π ζ₀ X F L' M' ρ' hρ' ζ (algebraMap R O κ) P hc hπ he
    hF2 hF1 hζ₀ (hprim n).pow_eq_one hP
  exact ⟨L', iA, iM, P, io, hio⟩

end GlobalTheory.CompanionTheory.Ar.HT.TestPts

namespace GlobalTheory.CompanionTheory.Ar.HT


open GlobalTheory.CompanionTheory.Ar.HT.TestPts in
theorem hasTestPoints_of_tate : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → Dc.HasTestPoints κ := by
  intro hPt E _ _ _ H D p _ R K _ _ _ _ _ _ _ _ n Ω _ _ _ _ Dc u hu S _ t x Γ₀ i hi L _ _ M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hTate hκ 𝔮 hq hh hpq
  obtain ⟨C, O, iF, iAC, iCZ, iR, iD, iAl, v, φ, hv, hp, hO, hinj, hcent⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.exists_complete_algClosed_center_of_height_one R p 𝔮 hq hh hpq
  letI : Algebra R O := φ.toAlgebra
  obtain ⟨-, -, hIC, -, hAC, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure p C v O hv hp hO
  haveI := hAC
  haveI := hIC
  have hgk : Function.Injective ((algebraMap O (FractionRing O)).comp φ) :=
    (IsFractionRing.injective O _).comp hinj
  let f : FractionRing R →+* FractionRing O := IsFractionRing.lift hgk
  have hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r) :=
    fun r => IsFractionRing.lift_algebraMap hgk r
  obtain ⟨I, hI1, hI2⟩ := hTate (FractionRing O) f
  have hz : spMap f ≫ (BT.genPt R).hom ≫ x = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hf
  obtain ⟨L', iA', iM', P, io, hio⟩ := reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀ i hi L M ρ hρ j hj π ζ₀ κ hc hπ he
    hrank hprop hκ C O v hv hp hO hinj f hf _ hz I hI1 hI2
  exact ⟨C, O, iF, iAC, iCZ, iR, iAl, v, φ, C ⊗[ℤ] D.La, C ⊗[O] Module.Dual O L', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P, io, hv, hinj, hcent, hio⟩

end GlobalTheory.CompanionTheory.Ar.HT
end
end

