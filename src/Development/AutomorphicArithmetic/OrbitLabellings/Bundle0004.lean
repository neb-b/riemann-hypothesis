module

public import Mathlib
public import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0030
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0008
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfLabelSetArith
section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private theorem UpperTheory.extend_sigma_coefficients_by_zero {A C W : Type} [Fintype A] [Field C] [AddCommGroup W] [Module C W] (m : A → ℕ)
    (e : (Σ s : A, Fin (m s)) → W) (a : A) (b : Fin (m a) → C) :
    ∃ b' : (Σ s : A, Fin (m s)) → C, (∀ q, q.1 ≠ a → b' q = 0) ∧ ∑ x, b x • e ⟨a, x⟩ = ∑ q, b' q • e q := by
  refine ⟨fun q => if h : q.1 = a then b (h ▸ q.2) else 0, fun q hq => dif_neg hq, ?_⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem UpperTheory.labelSetGeo_of_labelSetArith :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    LabSGeo C3 ι Y lab := by
  intro E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY Orb _ d _ lab ha
  have hsep1 : ∀ o (s s' : ZMod d), s ≠ s' →
      ∃ a : 𝓞 E, V.v (emA3 io ι (lab.tau o s) a - emA3 io ι (lab.tau o s') a) = 0 :=
    fun o s s' h => ha.sep (o, s) (o, s') fun e => h (Prod.mk.inj e).2
  have hgeo := fun o => _root_.GlobalTheory.SeparatedDirections.directions_typed_basis E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY (ZMod d) (lab.tau o) (hsep1 o)
  refine { em_int := fun _ _ x => embedding_integral ι _ x
           em_conj := ?_
           e_int := fun _ _ i => a3uvec_int C3 hι _ i
           e_eig := fun o x a => (hgeo o).2.1 x.1 x.2 a
           e_sat := ?_
           e_full := ?_ }
  · intro o a x
    rw [← ha.conj o a]
    exact (embedding_conjugate hstar ι _ x).symm
  · intro o
    obtain ⟨w, h1, h2⟩ := (hgeo o).2.2.1
    exact ⟨w, h1, fun q q' => (h2 q q').trans (by congr)⟩
  · intro o a v hv
    obtain ⟨b, hb⟩ := (hgeo o).2.2.2 a v hv
    obtain ⟨b', h1, h2⟩ := UpperTheory.extend_sigma_coefficients_by_zero (fun s => Dw.mult (lab.tau o s)) (selfLieBasisVector C3 ι lab o) a b
    exact ⟨b', h1, hb.trans h2⟩
end

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.ValBlocksSOfBlkMemS
section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.valBlocksS_of_blkMemS :
    ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (hd : ZMod d), hd + hd = 0 →
    ∀ (Orb : Type) [Fintype Orb] (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ),
    ValO X n FFimg ν → ∀ (F : ∀ o, RF.Flag (X o)) (nW : ℕ), nW ≤ 2 * n + 1 → ∀ ga : Orb → ZMod d → ℕ → ℕ,
    PlaneBlockProductsMemFamily hd X n F FFimg ga → (∀ o, (X o).Alt) → (∀ o, (X o).j' < (X o).n) →
    (∀ o s, (X o).rkF 1 (s + hd) = (X o).rkF 0 s) → (∀ o s k, ga o s k ≠ 0 → k ≤ (X o).rkF 0 s) →
    ValBlocksS hd X F nW ga ν := by
  intro C _ _ V d _ hd hhd Orb _ I J _ _ X n FFimg ν hV F nW hnW ga hMem hAlt hj hrk hga
  intro L hAtt hOne hRows hWt
  have hwt : ∀ o, ∀ q ∈ L o, ∀ (g : Fin 2) (a : ZMod d) (k : ℕ),
      GlobalTheory.wt (X o) q.1 g a k ≠ 0 → k ≤ (X o).rkF g a := by
    intro o q hq g a k hne
    fin_cases g
    · have hle : GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k ≤ ga o a k := by
        rw [← hWt o a k]
        exact le_sum_map (L o) (fun q => GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k) hq
      apply hga o a k
      have : GlobalTheory.wt (X o) q.1 0 a k ≠ 0 := hne
      omega
    · have hs : a + hd + hd = a := by rw [add_assoc, hhd, add_zero]
      have hle : GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k ≤ ga o (a + hd) k := by
        rw [← hWt o (a + hd) k]
        exact le_sum_map (L o)
          (fun q => GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k) hq
      rw [hs] at hle
      have hne' : GlobalTheory.wt (X o) q.1 1 a k ≠ 0 := hne
      have h0 : ga o (a + hd) k ≠ 0 := by omega
      have := hga o (a + hd) k h0
      rw [← hrk o (a + hd), hs] at this
      exact this
  have hOK : ∀ o, ∀ q ∈ L o, GlobalTheory.AttainsOK (X o) (F o) q.1 q.2 := fun o q hq =>
    attainsOK_of (X o) (F o) (Or.inl (hAlt o)) (hj o) q.1 q.2 (hwt o q hq) (hAtt o q hq)
  have hsum : ∑ o, (List.map (fun q => Formalism.L2.FormalSeriesBounds.RF.GlobalTheory.what₂ (X o).n q.1) (L o)).sum ≤ n := by omega
  exact val_lists hV jetProd F L hOK hsum (hMem L hOne hWt)
end

