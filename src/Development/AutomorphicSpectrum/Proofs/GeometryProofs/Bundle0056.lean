module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0051
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRight
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem isPiece_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ U : X.Opens, IsPiece ξ U (chartSub x c) ∧ ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩
  refine ⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩
  refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)

theorem coordTie_int_inst {X : Scheme.{0}} {F : Type} [Field F] {ξ : Spec (CommRingCat.of F) ⟶ X} {κ : Type} {x : κ → F}
    (inst : Algebra ℤ F) (h : @CoordTie X F _ ℤ _ inst ξ κ x) : @CoordTie X F _ ℤ _ (Ring.toIntAlgebra F) ξ κ x := by
  rwa [Subsingleton.elim inst (Ring.toIntAlgebra F)] at h

theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b g : F} (hb : b ∈ R) (h : a * b = g) (hg : g ≠ 0) :
    locSub R a ≤ locSub R g := by
  refine (Subring.closure_le).2 (Set.union_subset (fun y hy => le_locSub R g hy) ?_)
  rintro _ rfl
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hg)
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (h ▸ hg)
  have e : a⁻¹ = b * g⁻¹ := by rw [← h]; field_simp
  rw [SetLike.mem_coe, e]
  exact (locSub R g).mul_mem (le_locSub R g hb) (inv_mem_locSub R g)

theorem flag_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hT hall hVB hTw hc hT' hall' hdom hch
  classical
  have hi : Function.Injective (algebraMap Ω (GenField Ω r)) := (algebraMap Ω (GenField Ω r)).injective
  refine _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces X X' Ω (GenField Ω r) ξ ξ' f (algebraMap Ω (GenField Ω r)) hT.gen hT'.gen hdom (fun p' => ?_)
  let P' : Cpt ξ' := ⟨p', hall' p'⟩
  obtain ⟨⟨c₀, J⟩, hcJ⟩ := hT'.cover P'
  have hy0 : flagCoord κ x φ c (c₀, J) ≠ 0 := hcJ.1
  have hx0 : x c₀ ≠ 0 := by
    intro h0
    apply hy0
    simp [flagCoord, h0]

  have hover : ∀ Q' : Cpt ξ', InChart ξ' (flagCoord κ x φ c) ((c₀, J) : FlagIx κ n r) Q' →
      InChart ξ x c₀ ⟨f Q'.1, hall _⟩ := by
    intro Q' hQ
    refine (hch Q' c₀ (hall _)).2 ⟨by simpa using hx0, fun k => ?_⟩
    have h := hQ.2 ((k, J) : FlagIx κ n r)
    have hpr : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det) ≠ 0 := by
      intro h0
      apply hy0
      simp [flagCoord, h0]
    have e : flagCoord κ x φ c ((k, J) : FlagIx κ n r) / flagCoord κ x φ c ((c₀, J) : FlagIx κ n r) =
        algebraMap Ω (GenField Ω r) (x k) / algebraMap Ω (GenField Ω r) (x c₀) := by
      simp only [flagCoord]
      have : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
      field_simp
    rwa [e] at h
  let P : Cpt ξ := ⟨f p', hall _⟩
  have h2 : InChart ξ x c₀ P := hover P' hcJ
  have hfr := fun s => _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame X Ω ξ E κ x (r s) (V s) (L s) (m s) (n s) (φ s) (c s) c₀ P hT hall (hVB s) (hTw s) (hc s) h2
  choose g hgR hgu T M N hT0 hM hN hNM hφ using hfr
  let g₀ : Ω := ∏ s, g s
  have hg₀R : g₀ ∈ chartSub x c₀ := Subring.prod_mem _ fun s _ => hgR s
  have hg₀0 : g₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (hgu s).1
  have hreg : ∀ a ∈ chartSub x c₀, ∀ Q : Cpt ξ, InChart ξ x c₀ Q → a ∈ regAt ξ Q := fun a ha Q hQ =>
    (hT.ring c₀ hx0 a).1 ha Q hQ
  have hg₀inv : g₀⁻¹ ∈ regAt ξ P := by
    have : g₀⁻¹ = ∏ s, (g s)⁻¹ := by simp [g₀]
    rw [this]
    exact Subring.prod_mem _ fun s _ => (hgu s).2.2
  have hg₀u : unitAt ξ P g₀ := ⟨hg₀0, hreg _ hg₀R P h2, hg₀inv⟩
  let R : Subring Ω := locSub (chartSub x c₀) g₀
  have hle : ∀ s, locSub (chartSub x c₀) (g s) ≤ R := fun s =>
    locSub_le_of_mul (b := ∏ s' ∈ Finset.univ.erase s, g s')
      (Subring.prod_mem _ fun s' _ => hgR s') (Finset.mul_prod_erase Finset.univ g (Finset.mem_univ s)) hg₀0
  have hRP : ∀ a ∈ R, a ∈ regAt ξ P := by
    have : R ≤ regAt ξ P := (Subring.closure_le).2 (Set.union_subset (fun y hy => hreg y hy P h2)
      (by rintro _ rfl; exact hg₀inv))
    exact this
  obtain ⟨hPh, hdom1, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom P'
  have hRO : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ regAt ξ' P' := fun a ha => hdom1 a (hRP a ha)
  haveI : IsLocalRing (regAt ξ' P') := (regAt_isLocalRing_isFractionRing_stalk X' _ ξ' hT'.gen P').1
  have hscale : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), _ :=
    fun k J' => flagCoord_eq (m := m) x hφ k J'
  have hax : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
  have hprod0 := hscale c₀ J
  have hβ0 : ∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0 := by
    intro q h0
    apply hy0
    rw [hprod0, Finset.prod_eq_zero (Finset.mem_univ q) (by rw [h0, mul_zero]), mul_zero]
  have hβJ : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ regAt ξ' P' := by
    intro q J'
    have h := hcJ.2 ((c₀, Function.update J q J') : FlagIx κ n r)
    rw [hscale c₀ (Function.update J q J'), hprod0, mul_div_mul_left _ _ hax,
      prod_update_div (β := fun q => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => (algebraMap Ω (GenField Ω r) (x c₀) ^ m q.1) ^ ((q.2 : ℕ) + 1) * stepMinor (flagB M T q.1) q.2 b) J
        (fun q => mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hax)) (hβ0 q)) q J',
      mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hax))] at h
    exact h
  obtain ⟨t, htR, ht0, htO, htiO, hmap, hsm⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth Ω S r n R (regAt ξ' P') T M N J hRO hT0
    (fun s j l => hle s (hM s j l)) (fun s l j => hle s (hN s l j)) hNM hβ0 hβJ
  obtain ⟨hgA, hAeq⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing Ω E κ x S r n m φ c M T c₀ J g₀ hx0 hg₀R hg₀0 hφ hβ0
  obtain ⟨U₀, hU₀, hU₀m⟩ := isPiece_chart hT hx0
  obtain ⟨U₁, hU₁, hU₁m⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ g₀ hT.gen hU₀ hg₀R hg₀0
  obtain ⟨W₀, hW₀, hW₀m⟩ := isPiece_chart (coordTie_int_inst _ hT') hy0
  have hig0 : algebraMap Ω (GenField Ω r) g₀ ≠ 0 := by simpa using hg₀0
  obtain ⟨W₁, hW₁, hW₁m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₀ _ _ hT'.gen hW₀ hgA hig0
  rw [hAeq] at hW₁
  obtain ⟨W₂, hW₂, hW₂m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₁ _ t hT'.gen hW₁ htR ht0
  refine ⟨U₁, W₂, R, _, hmap, hU₁, hW₂, ?_, ?_, hsm⟩
  · intro q' hq'
    let Q' : Cpt ξ' := ⟨q', hall' q'⟩
    have e1 := ((hW₂m Q').1 hq').1
    obtain ⟨e2, e3⟩ := (hW₁m Q').1 e1
    have e4 := (hW₀m Q').1 e2
    have e5 := hover Q' e4
    obtain ⟨h', -, hun⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom Q'
    exact (hU₁m ⟨f q', hall _⟩).2 ⟨(hU₀m _).2 e5, hun hT'.gen g₀ (hreg _ hg₀R _ e5) e3⟩
  · refine (hW₂m P').2 ⟨(hW₁m P').2 ⟨(hW₀m P').2 hcJ, hig0, hRO _ (le_locSub _ _ hg₀R), ?_⟩, ht0, htO, htiO⟩
    rw [← map_inv₀]
    exact hRO _ (inv_mem_locSub _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartTransitionIntegral
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.Overlap

theorem omHT_pow_smul_mem : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R N V), (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin N → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ R) • w) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ a ∈ chartRing o (mseg y) s.1, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n * a ∈ chartRing o (mseg y) t.1) → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ' := by
  intro o _ Ω _ _ K _ J _ y E _ _ c p R N V _ _ Dc hom hh hρ hring s t σ'
  set f : Ω := mseg y s.1 / mseg y t.1 with hf
  have hfA : f ∈ chartRing o (mseg y) t.1 := Algebra.subset_adjoin ⟨s.1, rfl⟩
  have hfMn : ∀ n : ℕ, ∀ z ∈ (Dc t).om', f ^ n • z ∈ (Dc t).om' := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
      intro z hz
      rw [pow_succ', mul_smul]
      exact (Dc t).om'.smul_mem (⟨f, hfA⟩ : chartRing o (mseg y) t.1) (ih z hz)
  let P : Submodule (chartRing o (mseg y) s.1) V :=
    { carrier := {z | ∃ n : ℕ, f ^ n • z ∈ (Dc t).om'}
      add_mem' := by
        rintro a b ⟨n, hn⟩ ⟨m, hm⟩
        refine ⟨n + m, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [add_comm, pow_add, mul_smul]; exact hfMn m _ hn
        · rw [pow_add, mul_smul]; exact hfMn n _ hm
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro a z ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hring s t (a : Ω) a.2
        refine ⟨n + m, ?_⟩
        have e1 : f ^ (n + m) • (a • z) = (⟨f ^ m * a, hm⟩ : chartRing o (mseg y) t.1) • (f ^ n • z) := by
          show f ^ (n + m) • ((a : Ω) • z) = (f ^ m * a) • (f ^ n • z)
          rw [smul_smul, smul_smul]; congr 1; ring
        rw [e1]; exact (Dc t).om'.smul_mem _ hn }
  have hle : (Dc s).om' ≤ P := by
    unfold HTChart.om'
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨δ, rfl⟩
      obtain ⟨n, w, hw, he⟩ := hh s t δ
      refine ⟨n, ?_⟩
      have e2 : f ^ n • (Dc s).h δ = f ^ n • (Dc t).h δ + ((p : Ω) ^ R) • w := by
        rw [← he, smul_sub]; abel
      rw [e2]
      refine add_mem (hfMn n _ ?_) ?_
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨δ, rfl⟩)
      · refine Submodule.mem_sup_right ⟨w, hw, ?_⟩
        simp [Subalgebra.smul_def]
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨n, hn⟩ := hom s t u hu
      refine ⟨n, ?_⟩
      refine Submodule.mem_sup_right ⟨f ^ n • u, hn, ?_⟩
      simp [Subalgebra.smul_def, smul_comm ((p : Ω) ^ R) (f ^ n) u]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨n, hn⟩ := hle hz
  refine ⟨n, ⟨f ^ n • z, hn, ?_⟩⟩
  show eigProj (Dc t).ρΩ σ' (f ^ n • z) = f ^ n • eigProj (Dc s).ρΩ σ' z
  rw [hρ s t, map_smul]

end GlobalTheory.CompanionTheory.Ar.HT.Overlap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralAtPrimeInS
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem pow_smul_mem_om_of_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (w : Module.Dual Ω 𝔐.Li), (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) → ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • w ∈ (Dc t).om := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS o _ _ ho Dc hfam s t w hw
  have hp : p.Prime := Fact.out
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hs0 : mseg y s.1 ≠ 0 := s.2
  have ht0 : mseg y t.1 ≠ 0 := t.2
  have hfA : (mseg y s.1 / mseg y t.1) ∈ chartRing ℤ (mseg y) t.1 := div_mem_chartRing (mseg y) t.1 s.1
  have hle : ∀ a ∈ chartRing ℤ (mseg y) t.1, a ∈ chartRing o (mseg y) t.1 := by
    intro a ha
    have h2 : chartRing ℤ (mseg y) t.1 ≤ (chartRing o (mseg y) t.1).restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := o))
    exact h2 ha
  have hsm : ∀ a ∈ chartRing o (mseg y) t.1, ∀ e ∈ (Dc t).om, a • e ∈ (Dc t).om := by
    intro a ha e he
    have := (Dc t).om.smul_mem (⟨a, ha⟩ : chartRing o (mseg y) t.1) he
    rwa [Subalgebra.smul_def] at this
  have hinv : ∀ b : ℕ, ¬ p ∣ b → ((b : Ω))⁻¹ ∈ chartRing o (mseg y) t.1 := by
    intro b hb
    obtain ⟨r, hr⟩ := (ho ((b : Ω))⁻¹).2 ⟨1, b, hb, by simp⟩
    rw [← hr]
    exact Subalgebra.algebraMap_mem _ r
  by_contra hcon
  push_neg at hcon
  let I : Ideal (chartRing ℤ (mseg y) t.1) :=
    { carrier := {a | (a : Ω) • w ∈ (Dc t).om}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_smul]
        exact hsm _ (hle _ a.2) _ hu }
  let T : Submonoid (chartRing ℤ (mseg y) t.1) :=
    { carrier := {u | ∃ b n : ℕ, ¬ p ∣ b ∧ (b : Ω) ≠ 0 ∧ (u : Ω) = (b : Ω) * (mseg y s.1 / mseg y t.1) ^ n}
      one_mem' := ⟨1, 0, hp.not_dvd_one, by simp, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, n, hb, hb0, hu⟩ ⟨b', n', hb', hb0', hv⟩
        refine ⟨b * b', n + n', fun h => (hp.dvd_mul.1 h).elim hb hb', by push_cast; exact mul_ne_zero hb0 hb0', ?_⟩
        rw [Subalgebra.coe_mul, hu, hv]
        push_cast
        ring }
  have hdisj : Disjoint (I : Set (chartRing ℤ (mseg y) t.1)) (T : Set (chartRing ℤ (mseg y) t.1)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, n, hb, hb0, hub⟩
    have hu' : ((b : Ω) * (mseg y s.1 / mseg y t.1) ^ n) • w ∈ (Dc t).om := by rw [← hub]; exact hu
    have h2 := hsm _ (hinv b hb) _ hu'
    rw [smul_smul, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul] at h2
    exact hcon n h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨q, hq, hqP⟩ := TieVB.exists_point hT ht0 P hP
  have notP : ∀ u ∈ T, u ∉ P := fun u hu huP => Set.disjoint_left.1 hPT huP hu
  have hfu : unitAt 𝔐.ξ q (mseg y s.1 / mseg y t.1) := by
    by_contra hn
    exact notP ⟨(mseg y s.1 / mseg y t.1), hfA⟩ ⟨1, 1, hp.not_dvd_one, by simp, by simp⟩ ((hqP ⟨(mseg y s.1 / mseg y t.1), hfA⟩).2 hn)
  have hOver : OverZp 𝔐 p q := by
    intro r hr hfib
    by_contra hrp
    have hrp' : ¬ p ∣ r := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm
    by_cases hr0 : (r : Ω) = 0
    · apply hcon 0
      rw [pow_zero, one_smul, hfam.om_iff t w]
      intro q' _ hq'
      exact absurd (hq' r hr (fun hu => hu.1 hr0)) hrp
    have hrT : (r : chartRing ℤ (mseg y) t.1) ∈ T :=
      ⟨r, 0, hrp', hr0, by simp⟩
    have hu := not_not.1 (mt (hqP (r : chartRing ℤ (mseg y) t.1)).2 (notP _ hrT))
    apply hfib
    simpa using hu
  have hqs : InChart 𝔐.ξ (mseg y) s.1 q := by
    refine ⟨hs0, fun c' => ?_⟩
    have he : mseg y c' / mseg y s.1 = mseg y c' / mseg y t.1 * (mseg y s.1 / mseg y t.1)⁻¹ := by
      rw [inv_div]
      field_simp
    rw [he]
    exact mul_mem (hq.2 c') hfu.2.2
  have hwq := hw q hqs hq hOver
  rw [hfam.om_loc t q hq hOver] at hwq
  obtain ⟨s₀, hs₀A, hs₀u, hs₀M⟩ := TieVB.exists_den_span hT hq ((Dc t).om.toAddSubgroup)
    (fun a ha e he => hsm a (hle a ha) e he)
    (show w ∈ Submodule.span _ (((Dc t).om.toAddSubgroup : Set (Module.Dual Ω 𝔐.Li))) from hwq)
  have hI : (⟨s₀, hs₀A⟩ : chartRing ℤ (mseg y) t.1) ∈ I := hs₀M
  exact (hqP ⟨s₀, hs₀A⟩).1 (hIP hI) hs₀u

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigLat

theorem mem_eigSp_iff' {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {x : W} : x ∈ eigSp ρ τ ↔ ∀ a, ρ a x = τ a • x := by
  simp [eigSp, sub_eq_zero]

theorem sum_smul_of_eig {k W O : Type} [Field k] [AddCommGroup W] [Module k W] [CommRing O]
    {ρ : O →+* Module.End k W} {τ : O →+* k} {n : ℕ} (a c : Fin n → O) {x : W}
    (hx : ∀ b, ρ b x = τ b • x) :
    ∑ m, τ (c m) • ρ (a m) x = τ (∑ m, c m * a m) • x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hx, smul_smul, map_sum, map_mul, Finset.sum_smul]

theorem span_inf_eigSp : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ R R' L hj hρ hiR hL hσ hd
  obtain ⟨n, a, c, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir F
  have hd0 : ((NumberField.discr F : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (NumberField.discr_ne_zero F)
  have hσd : σ (∑ m, c m * a m) = ((NumberField.discr F : ℤ) : Ω) := by rw [hsum, map_intCast]
  have hiσd : (i.comp σ) (∑ m, c m * a m) = i ((NumberField.discr F : ℤ) : Ω) := by
    rw [RingHom.comp_apply, hσd]
  have hid0 : i ((NumberField.discr F : ℤ) : Ω) ≠ 0 := (map_ne_zero i).2 hd0

  let P : V → V := fun v => ((NumberField.discr F : ℤ) : Ω)⁻¹ • ∑ m, σ (c m) • ρ (a m) v

  let P' : Module.End Ω' V' := (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m)
  have hP'apply : ∀ x, P' x = (i ((NumberField.discr F : ℤ) : Ω))⁻¹ • ∑ m, (i.comp σ) (c m) • ρ' (a m) x := by
    intro x
    simp [P', LinearMap.sum_apply]
  have hPeig : ∀ v, P v ∈ eigSp ρ σ := by
    intro v
    refine mem_eigSp_iff'.2 fun b => ?_
    simp only [P]
    rw [map_smul, heq Ω V ρ σ b v, smul_comm]
  have hPL : ∀ v ∈ L, P v ∈ L := by
    intro v hv
    have h1 : (∑ m, σ (c m) • ρ (a m) v) ∈ L := by
      refine Submodule.sum_mem _ fun m _ => ?_
      exact L.smul_mem ⟨σ (c m), hσ _⟩ (hL _ _ hv)
    exact L.smul_mem ⟨_, hd⟩ h1
  have hjP : ∀ v, P' (j v) = j (P v) := by
    intro v
    rw [hP'apply]
    simp only [P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj.1, map_inv₀, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hj.1, hρ, RingHom.comp_apply]
  have hP'id : ∀ x ∈ eigSp ρ' (i.comp σ), P' x = x := by
    intro x hx
    rw [hP'apply, sum_smul_of_eig a c (mem_eigSp_iff'.1 hx), hiσd, smul_smul,
      inv_mul_cancel₀ hid0, one_smul]
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx2' : x ∈ eigSp ρ' (i.comp σ) := hx2
    have key : ∀ y ∈ Submodule.span R' (j '' (L : Set V)), P' y ∈ Submodule.span R'
        (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨e, he, rfl⟩ := hy
        rw [hjP]
        exact Submodule.subset_span ⟨P e, Submodule.mem_inf.2 ⟨hPL e he, hPeig e⟩, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        have h1 : P' (r • y) = r • P' y := by
          rw [Subring.smul_def, Subring.smul_def, map_smul]
        rw [h1]
        exact Submodule.smul_mem _ r hy
    have h2 := key x hx1
    rwa [hP'id x hx2'] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨he1, he2⟩ := Submodule.mem_inf.1 he
    have he2' : e ∈ eigSp ρ σ := he2
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨e, he1, rfl⟩, ?_⟩
    show j e ∈ eigSp ρ' (i.comp σ)
    refine mem_eigSp_iff'.2 fun b => ?_
    rw [hρ, mem_eigSp_iff'.1 he2', hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelTwistedComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieIntertwining

theorem act_intertwine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (Ω : Type) [Field Ω]
    (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (tΩ : SAB H (Sp Ω))
    (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ') (V V' : Type) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V')
    (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (φ : V ≃ₗ[Ω] V'),
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M.pt v).left ∧ w.left ≫ m'.φ = (M'.pt (φ v)).left) →
    ∀ a v, φ (ρ (g.s a) v) = ρ' a (φ v) := by
  intro E _ _ _ H g Ω _ X X' ξ ξ' t t' tΩ m m' V V' _ _ _ _ M M' ρ ρ' φ hM hM' tie a v
  obtain ⟨w, hw, hw'⟩ := tie v
  obtain ⟨w₃, hw₃, hw₃'⟩ := tie (ρ (g.s a) v)

  have h1 : (M.pt (ρ (g.s a) v)).left = (M.pt v).left ≫ (t.act.act (g.s a)).left := by
    rw [hM (g.s a) v]; rfl
  have h2 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ m.φ = w₃.left ≫ m.φ := by
    rw [hw₃, h1, ← hw, Category.assoc, Category.assoc, m.act]
  have h3 : (w.left ≫ (tΩ.act.act (g.s a)).left) ≫ tΩ.G.hom = w₃.left ≫ tΩ.G.hom := by
    rw [Category.assoc, Over.w, Over.w, Over.w]
  have h4 : w.left ≫ (tΩ.act.act (g.s a)).left = w₃.left := m.cart.1.hom_ext h2 h3
  have h5 : (M'.pt (φ (ρ (g.s a) v))).left = (M'.pt (ρ' a (φ v))).left := by
    have h6 : (tΩ.act.act (g.s a)).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
    rw [← hw₃', ← h4, hM' a (φ v), Over.comp_left, ← hw']
    exact (Category.assoc _ _ _).trans ((congrArg (w.left ≫ ·) h6).trans (Category.assoc _ _ _).symm)
  exact M'.inj (Over.OverMorphism.ext h5)

end GlobalTheory.CompanionTheory.Ar.LieIntertwining
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalence
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.CompMem

theorem blockWeight_weight_apply {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  · intro b _ hb
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]
  · simp

theorem comp_mem : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  intro K _ _ ι _ P hP f hf b
  obtain ⟨S, hS, rfl⟩ := hP
  classical
  letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)
  refine weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b
  refine Ideal.homogeneous_span _ S fun g hg => ?_
  obtain ⟨a, ha⟩ := hS g hg
  refine ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩
  funext k
  rw [blockWeight_weight_apply]
  exact ha m (mem_support_iff.2 hm) k

end GlobalTheory.CompanionTheory.Ggeo.CompMem
end

