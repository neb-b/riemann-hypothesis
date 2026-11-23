module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties

@[expose] public section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open GlobalTheory.SW.Lev
open Formalism.L2.Pj
open scoped Classical

namespace GlobalTheory.Dict.TieModel

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem exists_gen_one {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) (A : Submodule (𝓞 E) E) (hA : A.FG) :
    ∃ p ∈ A, A ≤ Submodule.span (𝓞 E) {p} ⊔ 𝔪 • A := by
  by_cases hb : A = ⊥
  · exact ⟨0, zero_mem _, by simp [hb]⟩
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hA
  have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  let f : 𝓞 E →ₗ[𝓞 E] E := LinearMap.toSpanSingleton (𝓞 E) E (d : E)⁻¹
  have hf (a : 𝓞 E) : f a = (a : E) * (d : E)⁻¹ := rfl
  let I : Ideal (𝓞 E) := A.comap f
  have hI : Submodule.map f I = A := by
    refine Submodule.map_comap_eq_self fun x hx => ?_
    obtain ⟨a, ha⟩ := hint x hx
    refine ⟨a, ?_⟩
    have : (a : E) = (d : E) * x := ha
    rw [hf, this]; field_simp
  have hI0 : I ≠ ⊥ := fun h => hb (by rw [← hI, h, Submodule.map_bot])
  obtain ⟨p, hp⟩ := IsDedekindDomain.exists_sup_span_eq (I := 𝔪 * I) (J := I) Ideal.mul_le_right
    (mul_ne_zero h0 hI0)
  have hpI : p ∈ I := hp ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self p)
  refine ⟨f p, hpI, ?_⟩
  conv_lhs => rw [← hI, ← hp]
  rw [Submodule.map_sup, sup_comm]
  refine sup_le_sup ?_ ?_
  · rw [Ideal.span, Submodule.map_span, Set.image_singleton]
  · rw [← smul_eq_mul, Submodule.map_smul'', hI]

theorem exists_gens {𝔪 : Ideal (𝓞 E)} (h0 : 𝔪 ≠ ⊥) : ∀ (r : ℕ) (L : Submodule (𝓞 E) (Fin r → E)), L.FG →
    ∃ β : Fin r → Fin r → E, (∀ i, β i ∈ L) ∧ L ≤ Submodule.span (𝓞 E) (Set.range β) ⊔ 𝔪 • L := by
  intro r
  induction r with
  | zero => exact fun L _ => ⟨fun i => i.elim0, fun i => i.elim0, fun v _ => by
      rw [Subsingleton.elim v 0]; exact zero_mem _⟩
  | succ r ih =>
    intro L hL
    let π : (Fin (r + 1) → E) →ₗ[𝓞 E] E := LinearMap.proj 0
    let ι : (Fin r → E) →ₗ[𝓞 E] (Fin (r + 1) → E) := LinearMap.vecCons 0 LinearMap.id
    have hι : Function.Injective ι := fun a b h => by
      simpa [ι] using h
    obtain ⟨_, ⟨b, hb, rfl⟩, hgen⟩ := exists_gen_one h0 (L.map π) (hL.map π)
    have hfg : (L.comap ι).FG :=
      Submodule.fg_of_fg_map_injective ι hι (Submodule.FG.of_le hL (Submodule.map_comap_le _ _))
    obtain ⟨β, hβ, hsp⟩ := ih _ hfg
    refine ⟨Fin.cons b fun i => ι (β i), fun i => Fin.cases hb (fun i => hβ i) i, fun v hv => ?_⟩
    have h1 := hgen ⟨v, hv, rfl⟩
    rw [← Set.image_singleton, ← Submodule.map_span, ← Submodule.map_smul'', ← Submodule.map_sup] at h1
    obtain ⟨w, hw, e⟩ := h1
    have hwL : w ∈ L := (sup_le (Submodule.span_le.2 (by simpa using hb)) Submodule.smul_le_right :
      _ ≤ L) hw
    have e2 : v - w = ι (Fin.tail (v - w)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · have : w 0 = v 0 := e
        simp [ι, this]
      · simp [ι, Fin.tail]
    have h2 : Fin.tail (v - w) ∈ L.comap ι := by
      rw [Submodule.mem_comap, ← e2]; exact sub_mem hv hwL
    have h3 := Submodule.mem_map_of_mem (f := ι) (hsp h2)
    rw [← e2, Submodule.map_sup, Submodule.map_smul'', Submodule.map_span] at h3
    rw [← sub_add_cancel v w]
    refine add_mem (SetLike.le_def.1 (sup_le_sup (Submodule.span_mono ?_)
      (Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _))) h3)
      (SetLike.le_def.1 (sup_le_sup_right (Submodule.span_mono ?_) _) hw)
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.succ, rfl⟩
    · rintro _ rfl
      exact ⟨0, rfl⟩

variable [IsCMField E] {r n : ℕ} {X : Data E r}

theorem cong_mono {𝔞 𝔟 : Ideal (𝓞 E)} (h : 𝔞 ≤ 𝔟) {u v : Fin r → E} (H : Cong X 𝔞 u v) : Cong X 𝔟 u v := by
  obtain ⟨s, hs, H⟩ := H
  obtain ⟨a, m, hm, e⟩ := cop_iff.1 hs
  exact ⟨s, cop_iff.2 ⟨a, m, h hm, e⟩, Submodule.smul_mono h le_rfl H⟩

variable {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem m_mem (l : Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ Mfr l :=
  (l.prod.ge.trans Ideal.mul_le_right) (Ideal.mem_span_singleton_self _)



end

end GlobalTheory.Dict.TieModel
