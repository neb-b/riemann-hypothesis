module

public import Mathlib
public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

abbrev frobOrder (D : D7) (p : ℕ) : ℕ := orderOf (zH D.R.toFrame (hP D p))

theorem frobOrder_spec (D : D7) {T p : ℕ} (hg : GIdx D.host T p) : 2 ≤ frobOrder D p ∧ Even (frobOrder D p) := by
  obtain ⟨hp, -, hc, hn, -⟩ := hg
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hL⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -⟩ := D.host.der.frob p (not_dvd_conductor_of_inert hp hc) P
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hPp, hL, σ, hσ, rfl⟩
  obtain ⟨P', hP', hL', σ', hσ', heq⟩ := Classical.epsilon_spec hne
  have hnF : frobOrder D p = orderOf (D.R.iota (hP D p)) := by
    unfold frobOrder
    rw [← Subgroup.orderOf_coe]
    exact orderOf_injective (MonoidHom.inr Formalism.FrobeniusOrbits.G0 D.R.MA) (fun a b hab => (Prod.ext_iff.1 hab).2) _
  have hev : Even (orderOf (D.R.iota (hP D p))) := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← heq]
    exact @hn P' hP' hL' σ' hσ'
  have hpos : 0 < orderOf (D.R.iota (hP D p)) := orderOf_pos _
  rw [hnF]
  obtain ⟨k, hk⟩ := hev
  exact ⟨by omega, k, hk⟩

section Pack

variable (D : D7) (u : D.what₂.Word)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
  (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ frobOrder D (D.what₂.places.resChar w))
  (he : Even (frobOrder D (D.what₂.places.resChar w)))
  (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
    (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
    (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ)

def pack : LocPack D u Lc (D.what₂.places.resChar w) where
  W := WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  Qq := QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  O := ORec D w (frobOrder D (D.what₂.places.resChar w))
  Kf := KfRec D w (frobOrder D (D.what₂.places.resChar w))
  ι := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φK.comp
    (iota (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  σ := sig (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  j := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φ.comp
    (jO (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  w := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φ
    (wU (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  hS := by
    let p := D.what₂.places.resChar w
    let n := frobOrder D p
    have h := (settingStd p n h5 h2 he).1
    let X := extRec D w n
    exact
      { prime := h.prime
        five_le := h.five_le
        two_le := h.two_le
        even := h.even
        frac_alt := h.frac_alt
        frac_O := X.frac
        p_unif := h.p_unif
        res_card := h.res_card
        eq_sum_herm_smul_frame_of_inW := h.eq_sum_herm_smul_frame_of_inW
        frob := h.frob
        period := h.period
        ι_comp := by
          intro x
          change X.φK (iota p n (algebraMap (WQ p n) (QQ p n) x)) = _
          rw [h.ι_comp, X.comm]
          rfl
        finite := X.fin.comp h.finite
        complete_O := X.complete
        w_sq := by
          change X.φ (wU p n) ^ 2 = (p : ORec D w n)
          rw [← map_pow, h.w_sq, map_natCast] }
  I := I
  ψ := ψ

end Pack

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ)

def packAll : ∀ u (w : D.what₂.places.Pl) (_h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    LocPack D u (Lc u) (D.what₂.places.resChar w) :=
  fun u w h => pack D u (Lc u) w h.2.1 (frobOrder_spec D h).1 (frobOrder_spec D h).2 (I u w h) (ψ u w h)

variable (hd : ∀ u w h, ((packAll D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev record : D7 := recG D sc Ce Lc (packAll D Lc I ψ) hd

end Record

end GlobalTheory.Mem.LocalPack
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo NumberField

namespace GlobalTheory.GeoGraft

variable {D : D7}

def graft (Xg X₀ : DivX D) (iM : ∀ j (c : Xg.Comp j), (X₀.MjH j).V →ₗ[D.what₂.LL] Xg.geo.Fn (Xg.Yv j c))
    (hiM : ∀ j c x, iM j c x ∈ Xg.geo.H0 (Xg.Yv j c) (Xg.Lw j c (DV.kapW D j))) : DivX D :=
  { Xg with
    MjH := X₀.MjH, MjH_good := X₀.MjH_good, jM := X₀.jM, jM_basis := X₀.jM_basis, jM_lat := X₀.jM_lat
    MjLat_sub := X₀.MjLat_sub, jM_metric := X₀.jM_metric
    Qp := X₀.Qp, degreeZero_partial_set_empty := X₀.degreeZero_partial_set_empty, Qp_muAt := X₀.Qp_muAt, Qp_g := X₀.Qp_g
    QPl := X₀.QPl, finQ := X₀.finQ, qv := X₀.qv, qv_gt := X₀.qv_gt, qv_char := X₀.qv_char
    nu := X₀.nu, nu_ne := X₀.nu_ne, nu_abs := X₀.nu_abs, ZQ := X₀.ZQ, quotientLocalValueFirst := X₀.quotientLocalValueFirst, typeDim := X₀.typeDim
    iMj := iM, iMj_mem := hiM
    logLam := X₀.logLam, logLam_base := X₀.logLam_base
    kapR := X₀.kapR, kapR_pos := X₀.kapR_pos, kapR_conj := X₀.kapR_conj }

def Keeps (X X₀ : DivX D) : Prop := ∃ Xg iM hiM, X = graft Xg X₀ iM hiM

def GeoOver (Q : DivX D → Prop) (X₀ : DivX D) : Prop :=
  ∃ (X : DivX D) (inK : X.Lev → ℕ → Prop), Keeps X X₀ ∧ GeoTiedP X inK ∧ Q X

end GlobalTheory.GeoGraft
end
end

