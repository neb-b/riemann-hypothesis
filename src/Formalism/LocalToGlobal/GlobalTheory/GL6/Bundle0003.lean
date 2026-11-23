module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes
public import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0006

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

section Min

variable (D : D7) (u : D.what₂.Word)

def HeckeIntegralLevelZero : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u 0 v) ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) ∧
    Into D u w (Dop D u 0 v) ((D.fm u).S 0 w) ((D.fm u).Bw 0 w v)

def HeckeRamifiedLevelZero : Prop :=
  ∀ v, ∀ φ ∈ MramI D u 0, Uop D u 0 v φ ∈ MramI D u 0 ∧ Dop D u 0 v φ ∈ MramI D u 0 ∧
    Uop D u 0 v (Dop D u 0 v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ

def SecondBranchInclusionLength : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)))

variable {D u}

theorem rational_level_zero_of_integral (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true) (h4 : HeckeIntegralLevelZero D u) :
    Rat0 D u := fun v =>
  ⟨rat_of_into w _ _ _ (h4 w hw hs v).1 ((D.fm u).Bw_span 0 w v),
    rat_of_into w _ _ _ (h4 w hw hs v).2 (S_span 0 w)⟩

theorem hecke_ramified_lattice_stable_length (hS : HidaSetting D u) (hR : Rat0 D u) (hB : SecondBranchInclusionLength D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u)
    (w : D.what₂.places.Pl) (hw : OverT D u w) {v : (D.mem u).A.vT} (hv : v ∈ VV D u w) :
    (Sram D u w).map (gR hR w v) ≤ Sram D u w ∧
    ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ)) ∧
      Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v)).comap (Sram D u w).subtype) ≤
        ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) := by
  obtain ⟨hs, ht⟩ := mem_VV hv
  have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) := hS.2.2 _ ht
  have hnb : ((nb D u w v : ℕ) : ℤ) = (D.fm u).bTop ((D.fm u).tauOf w v) := Int.toNat_of_nonneg hb
  obtain ⟨hUB, hDS⟩ := h4 w hw hs v
  obtain ⟨a1, n, a2, a3⟩ := hB w hw hs v hb
  rw [← hnb, tL_eq_map] at a1 a2
  have ram := h9 v
  refine ⟨?_, n, a3, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxB : (((D.mem u).A.T : ℕ) : Ow D w) ^ nb D u w v • x ∈ (D.fm u).Bw 0 w v := a1 ⟨x, hx.1, rfl⟩
    obtain ⟨y, hy, hy'⟩ := hUB _ hxB
    have e : gR hR w v x = y := by
      apply (D.fm u).emb_inj 0
      rw [hy', gR_spec, emb_smulR, map_smul]; simp
    rw [e]
    refine ⟨hy, mem_ramSub.mpr ?_⟩
    rw [← e, gR_spec]
    exact Submodule.smul_mem _ _ (ram _ (mem_ramSub.mp hx.2)).1
  · have h := LemmaC_core hR w hw v (nb D u w v) (fun x hx => a1 ⟨x, hx, rfl⟩) hUB hDS ram
    unfold len at a2
    rw [a2] at h
    exact_mod_cast h

theorem congruence_no_kernel_minimal (hS : HidaSetting D u) (hB : SecondBranchInclusionLength D u) (h4 : HeckeIntegralLevelZero D u) (h9 : HeckeRamifiedLevelZero D u) :
    CongruenceLatticeLengthBound D u := by
  intro w hw
  by_cases hs : (D.fm u).seenP w = true
  · have hR : Rat0 D u := rational_level_zero_of_integral w hw hs h4
    have hg : ∀ v ∈ (VV D u w).toList, (Sram D u w).map (gR hR w v) ≤ Sram D u w :=
      fun v hv => (hecke_ramified_lattice_stable_length hS hR hB h4 h9 w hw (Finset.mem_toList.mp hv)).1
    obtain ⟨hG, hGl⟩ := len_list_le (Sram D u w) (gR hR w) (VV D u w).toList hg
    obtain ⟨hP, hPl⟩ := len_pow_le (Sram D u w) (GR hR w (VV D u w).toList) hG D.R.m
    rw [Nlam_eq hS hR w]
    refine ⟨hP, ?_⟩
    have H : ∀ v : {v // v ∈ VV D u w}, ∃ n : ℕ, (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℚ) +
            (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℚ)) / (D.R.k : ℚ)) ∧
        Module.length (Ow D w) (Sram D u w ⧸ ((Sram D u w).map (gR hR w v.1)).comap (Sram D u w).subtype) ≤
          ((n + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) :=
      fun v => (hecke_ramified_lattice_stable_length hS hR hB h4 h9 w hw v.2).2
    choose nn hnq hnl using H
    have hsum : Module.length (Ow D w) (Sram D u w ⧸
        ((Sram D u w).map (GR hR w (VV D u w).toList ^ D.R.m)).comap (Sram D u w).subtype) ≤
        ((D.R.m * ∑ v ∈ (VV D u w).attach, (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℕ∞) := by
      refine le_trans hPl ?_
      push_cast
      rw [nsmul_eq_mul]
      refine mul_le_mul_right (le_trans hGl ?_) _
      rw [Finset.sum_map_toList, ← Finset.sum_attach]
      exact Finset.sum_le_sum (fun v _ => by exact_mod_cast hnl v)
    obtain ⟨n, hn, hle⟩ := ENat.le_natCast_iff.mp hsum
    refine ⟨n, hn, ?_⟩
    have hk : (0 : ℝ) < (D.R.k : ℝ) := by
      have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 0 < D.R.k)
    have he : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ (D.duS u : ℝ) := Nat.cast_nonneg _
    have hterm : ∀ v : {v // v ∈ VV D u w},
        ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) ≤
          (D.what₂.places.ramIdx w : ℝ) * (D.duS u * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
            (D.fm u).bTop ((D.fm u).tauOf w v.1))) := by
      intro v
      have ht := (mem_VV v.2).2
      have hb : 0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v.1) := hS.2.2 _ ht
      have hbR : (0 : ℝ) ≤ ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := by exact_mod_cast hb
      have hN1 := twist_le (u := u) ht
      have hq : ((nn v : ℕ) : ℝ) = (D.what₂.places.ramIdx w : ℝ) * ((D.duS u : ℝ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) := by
        have := congrArg (fun q : ℚ => (q : ℝ)) (hnq v)
        push_cast at this; exact this
      have hk1 : ((D.R.k - 1 : ℕ) : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast Nat.sub_le _ _
      push_cast
      rw [hq, mul_div_assoc, ← mul_add]
      apply mul_le_mul_of_nonneg_left _ he
      have e1 : (D.duS u : ℝ) * (((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v.1)) : ℝ) +
            (D.R.k : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ)) / (D.R.k : ℝ)) ≤
          (D.duS u : ℝ) * ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1)) :=
        mul_le_mul_of_nonneg_left hN1 hd
      have e2 : ((D.R.k - 1 : ℕ) : ℝ) * (D.duS u : ℝ) ≤ (D.duS u : ℝ) * (D.R.k : ℝ) := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hk1 hd
      have e3 : 0 ≤ (D.duS u : ℝ) * ((D.fm u).bTop ((D.fm u).tauOf w v.1) : ℝ) := mul_nonneg hd hbR
      nlinarith
    calc (n : ℝ) ≤ ((D.R.m * ∑ v ∈ (VV D u w).attach,
            (nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u)) : ℕ) : ℝ) := by exact_mod_cast hle
      _ = (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach,
            ((nn v + D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (D.R.m : ℝ) * ∑ v ∈ (VV D u w).attach, ((D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v.1) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v.1)))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hterm v)) (Nat.cast_nonneg _)
      _ = _ := by
          rw [Finset.sum_attach (VV D u w) (fun v => (D.what₂.places.ramIdx w : ℝ) * (D.duS u *
            ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k +
              (D.fm u).bTop ((D.fm u).tauOf w v)))), ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  · have hs' : (D.fm u).seenP w = false := by simpa using hs
    have hVV : VV D u w = ∅ := by simp [LT.VVT, hs']
    have hN : Nlam D u w = Sram D u w := by
      have := imgL_eq_map (u := u) w ((((D.mem u).A.T : ℂ) ^ LT.expT D u w) • (Uprod D u 0 w) ^ D.R.m) LinearMap.id
        (fun x => by simp [LT.expT, LT.Uprod, LT.VVT, hs']) (Sram D u w)
      rw [Submodule.map_id] at this
      exact this
    rw [hN, hVV]
    refine ⟨le_rfl, 0, ?_, by simp⟩
    unfold len
    rw [Submodule.comap_subtype_self]
    simp

end Min

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.DiamondCommDistinctPlaces
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem adelic_GL_ext_local (g h : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (H : ∀ w : HeightOneSpectrum (𝓞 F), bc (prV (E := E) w) g = bc (prV (E := E) w) h) : g = h := by
  ext i j
  have key : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w (g.1 i j - h.1 i j) = 0 := by
    intro w
    have := congrArg (fun x : GL (Fin n) (E ⊗[F] w.adicCompletion F) => x.1 i j) (H w)
    rw [map_sub]; exact sub_eq_zero.2 this
  exact sub_eq_zero.1 (Formalism.UG.P.afsplit_inj _ key)

theorem adelic_comm_disjoint_support (δ δ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v v' : HeightOneSpectrum (𝓞 F))
    (hvv : v ≠ v') (h1 : ∀ w, w ≠ v → bc (prV (E := E) w) δ = 1) (h2 : ∀ w, w ≠ v' → bc (prV (E := E) w) δ' = 1) :
    δ * δ' = δ' * δ := by
  apply adelic_GL_ext_local
  intro w
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw; rw [h2 w hvv, mul_one, one_mul]
  · rw [h1 w hw, mul_one, one_mul]

end Gen

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 1000000 in
theorem diamond_comm_distinct_places (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) (i : ℕ) (hi : i ≤ D.R.m) (v v' : (D.mem u).A.vT)
    (hvv : v ≠ v') (a : ((D.mem u).A.Fv v')ˣ) (b : ((D.mem u).A.Fv v)ˣ) (φ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i)
    (hφ : φ ∈ (D.fm u).Fi i) :
    Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ) = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b (Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a φ) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  have hval : ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
    intro c; funext z
    have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hgA : g ∈ AdFun (Tf.cls i hi).lev (embT D) := (Submodule.mem_inf.1 hg).1
  have hdia : ∀ v0 a0 (ψ : Formalism.MainNotions.product_first_zeroth_parts.Fn D u i) c,
      Formalism.MainNotions.product_first_zeroth_parts.dia D u i v0 a0 ψ c = (D.fm u).dilT i v0 a0 c (ψ ((D.fm u).dil i v0 a0 c)) := fun _ _ _ _ => rfl
  obtain ⟨ka, hka, δa, hδa⟩ := hE i hi v' a
  obtain ⟨kb, hkb, δb, hδb⟩ := hE i hi v b
  have hne : (Tf.atT.eV v).1 ≠ (Tf.atT.eV v').1 := fun h => hvv (Tf.atT.eV.injective (Subtype.ext h))
  have hcomm : δa * δb = δb * δa :=
    Subtype.ext (adelic_comm_disjoint_support δb.1 δa.1 _ _ hne hδb.1 hδa.1).symm
  have hga := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (level_places_not_bad Tf.atT v') hδa hgA
  have hgb := adelic_function_right_translate_diamond (Tf.cls i hi).lev (embT D) _ _ (level_places_not_bad Tf.atT v) hδb hgA
  funext c
  have e1 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v b φ ((D.fm u).dil i v' a c) =
      fun z => g ((Tf.cls i hi).y ((D.fm u).dil i v' a c) * δb) ((Tf.val i hi).eY z) := by
    rw [hdia, hval, (Tf.val i hi).dilT v b kb hkb _ δb hδb g hgA]
  have e2 : Formalism.MainNotions.product_first_zeroth_parts.dia D u i v' a φ ((D.fm u).dil i v b c) =
      fun z => g ((Tf.cls i hi).y ((D.fm u).dil i v b c) * δa) ((Tf.val i hi).eY z) := by
    rw [hdia, hval, (Tf.val i hi).dilT v' a ka hka _ δa hδa g hgA]
  rw [hdia v' a, e1, (Tf.val i hi).dilT v' a ka hka c δa hδa _ hgb,
    hdia v b, e2, (Tf.val i hi).dilT v b kb hkb c δb hδb _ hga]
  funext z
  simp only [mul_assoc, hcomm]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfFrobeniusSimilitude
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.DIV
open Formalism.GradedWeylDivisibility (blockAct)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem at_infinity_unitary (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (τ : ι) :
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ =
      gramC J emb τ := by
  have h : cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ =
      (cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (emb τ) := by
    ext a b
    simp [atInf, cT, conjTranspose_apply, hc]
  rw [e]
  simp only [gramC, atInf]
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

def frameTranslate (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]; exact (isUnit_det_atInf emb γ τ).mul (y.2 τ)⟩

theorem frame_translate_is_orthonormal (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) (hy : y.IsON) :
    (frameTranslate emb hc γ hγ y).IsON := fun τ => by
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) =
      (y.1 τ)ᴴ * ((atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ *
        atInf emb (γ : Matrix (Fin n) (Fin n) E) τ) * y.1 τ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  show (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = 1 ∨
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = -1
  rw [e, at_infinity_unitary emb hc γ hγ τ]
  exact hy τ

theorem at_infinity_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem adelic_value_translate (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (y : Frames (gramC J emb)) :
    g x' y = (S.chi κ : ℂ) * g x (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y) := by
  apply hg γ hγ x x' κ hx
  intro τ
  show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
    (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

theorem complex_span_block_action_stable (lam : ι → DomWeight n) (w : ι → Matrix (Fin n) (Fin n) ℂ)
    {P : MvPolynomial (ι × Fin n × Fin n) ℂ} (hP : P ∈ CSpan lam) : blockAct ℂ w P ∈ CSpan lam := by
  have h1 : CSpan lam ≤ VV ℂ lam := by
    refine (Formalism.L2.Col.CSpan_le_span (RingHom.id ℂ) lam).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    simpa [MvPolynomial.map_id] using hF'
  have h2 : blockAct ℂ w P ∈ VV ℂ lam :=
    (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n w).2 (fun τ => nablaSq ℂ n (lam τ)) (fun τ => nablaSq ℂ n (lam τ))
      (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ f hf) P (h1 hP)
  simpa [MvPolynomial.map_id] using Formalism.L2.Col.map_mem_CSpan (RingHom.id ℂ) lam _ h2

end Gen

variable {D : D7} {u : D.what₂.Word}

theorem embedding_conj_compat (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

theorem forms_from_adelic_function (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (hφ : φ ∈ (D.fm u).Fi i) :
    ∃ g ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i),
      ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  refine ⟨g, hg, fun c => ?_⟩
  funext z
  have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm



end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.LatticeInclusionOfSubIntegral
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

def bwA_N {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => if τ = τv then atInf (embT D) (B'⁻¹ * B : GL (Fin n) D.host.E).1 τ else 1

theorem bwA_N_mul {n : ℕ} (τv : D.what₂.Tau) (B B' : GL (Fin n) D.host.E) :
    (fun τ => bwA_N D τv B B' τ * atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ) =
      fun τ => if τ = τv then atInf (embT D) (B'⁻¹ : GL (Fin n) D.host.E).1 τ
        else atInf (embT D) (B⁻¹ : GL (Fin n) D.host.E).1 τ := by
  funext τ
  unfold bwA_N
  split_ifs with h
  · simp only [atInf]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  · rw [one_mul]

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedLatticePropsOfModel
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Parts

variable (D : D7) (u : D.what₂.Word)

def RamifiedSlopeFormula : Prop :=
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2)

end Parts

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

