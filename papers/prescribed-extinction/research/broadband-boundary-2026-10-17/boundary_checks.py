#!/usr/bin/env python3
"""Numerical diagnostic of the boundary note's narrow-resonance selection.

This is an ANALYTIC SURROGATE, NOT A MAXWELL OR DEVICE SIMULATION.
It checks algebra, local derivatives, numerical root selection, and sampled
global minima.  Dense grids are not continuum-band certificates.  In
particular, the holomorphic work surrogate is not asserted to be realizable
by a dielectric body, and no absorption-asymmetry ratio is computed.

Only Python's standard library and NumPy are required.  Run this file to
replace numerical_results.json beside it.  All tolerances and grids are
declared below.  No manuscript or other source file is modified.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import numpy as np


OMEGA_C = 1.5
BAND = (1.0, 2.0)
RHO = 0.02
TARGET = 1.7
Y_C = 1.0
S_MINUS = math.sqrt(TARGET / (2.0 * Y_C))
S_PLUS = math.sqrt(2.0 * TARGET / Y_C)
S_MID = (S_MINUS + S_PLUS) / 2.0
RIPPLE_AMPLITUDES = (6.0e-5, 3.0e-5)
RIPPLE_FREQUENCIES = (900.0, 1370.0)
BOWL_K = 0.08
QUADRATIC_WORK = 0.15 - 0.10j
WIDTHS = (0.03, 0.01, 0.003, 0.001, 0.0003, 0.0001, 0.00003)
SELECTED_WIDTH = WIDTHS[-1]
ROOT_TOLERANCE = 2.0e-14
FREQUENCY_GRID_COUNT = 200001
INNER_GRID_COUNT = 60001
INNER_GRID_HALF_WIDTH = 25.0


def bisect(function, lower, upper, tolerance=ROOT_TOLERANCE):
    """Safeguarded scalar root with an explicit sign bracket."""
    f_lower, f_upper = float(function(lower)), float(function(upper))
    if f_lower == 0.0:
        return float(lower)
    if f_upper == 0.0:
        return float(upper)
    if f_lower * f_upper > 0.0:
        raise ValueError(f"No root bracket: {lower}, {upper}, {f_lower}, {f_upper}")
    for _ in range(160):
        middle = (lower + upper) / 2.0
        f_middle = float(function(middle))
        if f_middle == 0.0 or upper - lower <= tolerance:
            return float(middle)
        if f_lower * f_middle <= 0.0:
            upper, f_upper = middle, f_middle
        else:
            lower, f_lower = middle, f_middle
    raise RuntimeError("Bisection did not terminate")


def golden_minimum(function, lower, upper, tolerance=2.0e-11):
    """Independent derivative-free local minimum for the Fano algebra check."""
    ratio = (math.sqrt(5.0) - 1.0) / 2.0
    left = upper - ratio * (upper - lower)
    right = lower + ratio * (upper - lower)
    f_left, f_right = function(left), function(right)
    for _ in range(160):
        if upper - lower <= tolerance:
            break
        if f_left < f_right:
            upper, right, f_right = right, left, f_left
            left = upper - ratio * (upper - lower)
            f_left = function(left)
        else:
            lower, left, f_left = left, right, f_right
            right = lower + ratio * (upper - lower)
            f_right = function(right)
    return (lower + upper) / 2.0


def coefficients(s):
    shift = s - S_MID
    return 0.25 + 0.015 * shift + 1j * (0.80 + 0.010 * shift)


def baseline(omega, s, derivative=0):
    """Fixed smooth bowl plus small rapid ripples; no linewidth dependence."""
    x = np.asarray(omega) - OMEGA_C
    phase1 = 0.90 + 0.40 * (s - S_MID)
    phase2 = -0.35 + 0.20 * (s - S_MID)
    amp1, amp2 = RIPPLE_AMPLITUDES
    freq1, freq2 = RIPPLE_FREQUENCIES
    if derivative == 0:
        return (1.0 + BOWL_K * x * x + amp1 * np.sin(freq1 * x + phase1)
                + amp2 * np.cos(freq2 * x + phase2))
    if derivative == 1:
        return (2.0 * BOWL_K * x + amp1 * freq1 * np.cos(freq1 * x + phase1)
                - amp2 * freq2 * np.sin(freq2 * x + phase2))
    if derivative == 2:
        return (2.0 * BOWL_K - amp1 * freq1**2 * np.sin(freq1 * x + phase1)
                - amp2 * freq2**2 * np.cos(freq2 * x + phase2))
    raise ValueError("Only derivatives 0, 1, 2 are implemented")


def ell(u):
    return 1.0 / (-np.asarray(u) - 1j)


def work_response(zeta, s):
    """Holomorphic nonlinear increment: F(zeta)-F(0)."""
    return coefficients(s) * zeta + QUADRATIC_WORK * zeta * zeta


def frozen_profile(u, s, derivative=0):
    denominator = -np.asarray(u) - 1j
    zeta = RHO / denominator
    zeta_prime = RHO / denominator**2
    if derivative == 0:
        return baseline(OMEGA_C, s) + np.imag(work_response(zeta, s))
    if derivative == 1:
        return np.imag((coefficients(s) + 2.0 * QUADRATIC_WORK * zeta) * zeta_prime)
    if derivative == 2:
        zeta_second = 2.0 * RHO / denominator**3
        return np.imag(2.0 * QUADRATIC_WORK * zeta_prime**2
                       + (coefficients(s) + 2.0 * QUADRATIC_WORK * zeta) * zeta_second)
    raise ValueError("Only derivatives 0, 1, 2 are implemented")


def frozen_minimum(s):
    linear = coefficients(s)
    u_linear = (linear.real + abs(linear)) / linear.imag
    return bisect(lambda u: frozen_profile(u, s, 1), u_linear - 0.6, u_linear + 0.6)


def lorentz(omega, gamma, v, derivative=0):
    """Exact positive-residue, positive-damping Lorentz oscillator."""
    omega = np.asarray(omega)
    omega_squared = OMEGA_C**2 - gamma * OMEGA_C * v
    residue = RHO * gamma * OMEGA_C
    # Algebraically identical factorization avoids subtracting two nearly
    # equal squared frequencies at the center of a very narrow resonance.
    denominator = ((OMEGA_C - omega) * (OMEGA_C + omega)
                   - gamma * OMEGA_C * v - 1j * gamma * omega)
    if derivative == 0:
        return residue / denominator
    first_denominator = -2.0 * omega - 1j * gamma
    if derivative == 1:
        return -residue * first_denominator / denominator**2
    if derivative == 2:
        return (2.0 * residue * first_denominator**2 / denominator**3
                + 2.0 * residue / denominator**2)
    raise ValueError("Only derivatives 0, 1, 2 are implemented")


def scaled_lorentz_jets(t, v, gamma):
    """Exact algebraic scaled form and every (t,v) derivative of order <=2."""
    denominator = (-v - t - gamma * t * t / (4.0 * OMEGA_C)
                   - 1j * (1.0 + gamma * t / (2.0 * OMEGA_C)))
    derivative_t = -1.0 - gamma * t / (2.0 * OMEGA_C) - 1j * gamma / (2.0 * OMEGA_C)
    second_t = -gamma / (2.0 * OMEGA_C)
    return {
        "value": RHO / denominator,
        "t": -RHO * derivative_t / denominator**2,
        "v": RHO / denominator**2,
        "tt": 2.0 * RHO * derivative_t**2 / denominator**3 - RHO * second_t / denominator**2,
        "tv": -2.0 * RHO * derivative_t / denominator**3,
        "vv": 2.0 * RHO / denominator**3,
    }


def normalized_spectrum(omega, s, gamma, v, derivative=0):
    """Surrogate Y; the cross-section surrogate is s^2 times this value."""
    zeta = lorentz(omega, gamma, v)
    if derivative == 0:
        return baseline(omega, s) + np.imag(work_response(zeta, s))
    zeta_prime = lorentz(omega, gamma, v, 1)
    response_prime = coefficients(s) + 2.0 * QUADRATIC_WORK * zeta
    if derivative == 1:
        return baseline(omega, s, 1) + np.imag(response_prime * zeta_prime)
    if derivative == 2:
        zeta_second = lorentz(omega, gamma, v, 2)
        return (baseline(omega, s, 2)
                + np.imag(2.0 * QUADRATIC_WORK * zeta_prime**2 + response_prime * zeta_second))
    raise ValueError("Only derivatives 0, 1, 2 are implemented")


def centered_location(s, gamma):
    u_reference = frozen_minimum(s)
    return bisect(lambda v: (gamma / 2.0) * normalized_spectrum(OMEGA_C, s, gamma, v, 1),
                  u_reference - 0.6, u_reference + 0.6)


def sampled_global_check(s, gamma, v):
    """A dense sampled check, explicitly not a continuum certificate."""
    full_grid = np.linspace(*BAND, FREQUENCY_GRID_COUNT)
    inner_t = np.linspace(-INNER_GRID_HALF_WIDTH, INNER_GRID_HALF_WIDTH, INNER_GRID_COUNT)
    inner_grid = OMEGA_C + gamma * inner_t / 2.0
    inner_grid = inner_grid[(inner_grid >= BAND[0]) & (inner_grid <= BAND[1])]
    grid = np.unique(np.concatenate((full_grid, inner_grid, [OMEGA_C])))
    values = normalized_spectrum(grid, s, gamma, v)
    center = float(normalized_spectrum(OMEGA_C, s, gamma, v))
    index = int(np.argmin(values))
    minimum_difference = float(values[index] - center)
    return {
        "sample_count": int(grid.size),
        "sampled_minimum_frequency": float(grid[index]),
        "sampled_minimum_offset_from_center": float(grid[index] - OMEGA_C),
        "sampled_minimum_minus_center": minimum_difference,
        "center_is_sampled_minimum_to_2e-12": bool(minimum_difference >= -2.0e-12),
        "scope": "Dense sampled check only; not a continuum-band certificate.",
    }


def main():
    s_reference = S_MID
    coefficient = coefficients(s_reference)
    a, b = coefficient.real, coefficient.imag
    d = abs(coefficient)
    u_formula = (a + d) / b

    def leading(u):
        return (a - b * u) / (1.0 + u * u)

    def leading_second(u):
        numerator = b * u * u - 2.0 * a * u - b
        return ((2.0 * b * u - 2.0 * a) / (1.0 + u * u)**2
                - 4.0 * u * numerator / (1.0 + u * u)**3)

    u_numeric = golden_minimum(leading, u_formula - 1.0, u_formula + 1.0)
    u_nonlinear = frozen_minimum(s_reference)
    finite_difference_step = 1.0e-4
    curvature_difference = ((leading(u_formula + finite_difference_step) - 2.0 * leading(u_formula)
                             + leading(u_formula - finite_difference_step)) / finite_difference_step**2)
    fano = {
        "A": a, "B1": b, "rho": RHO,
        "leading_minimum_location_formula": u_formula,
        "leading_minimum_location_golden_search": u_numeric,
        "location_absolute_difference": abs(u_formula - u_numeric),
        "leading_minimum_value_formula": (a - d) / 2.0,
        "leading_minimum_value_evaluated": leading(u_formula),
        "leading_curvature_formula": 2.0 * d / (1.0 + u_formula**2)**2,
        "leading_curvature_differentiated": leading_second(u_formula),
        "leading_curvature_finite_difference": curvature_difference,
        "finite_difference_step": finite_difference_step,
        "nonlinear_frozen_minimum_location": u_nonlinear,
        "nonlinear_frozen_minimum_depth": float(baseline(OMEGA_C, s_reference) - frozen_profile(u_nonlinear, s_reference)),
        "nonlinear_frozen_curvature": float(frozen_profile(u_nonlinear, s_reference, 2)),
        "nonlinear_frozen_derivative_residual": abs(float(frozen_profile(u_nonlinear, s_reference, 1))),
    }

    t_grid = np.linspace(-4.0, 4.0, 121)[:, None]
    v_grid = np.linspace(u_nonlinear - 0.6, u_nonlinear + 0.6, 91)[None, :]
    limit_jets = scaled_lorentz_jets(t_grid, v_grid, 0.0)
    omega_grid = np.linspace(*BAND, FREQUENCY_GRID_COUNT)
    convergence = []
    linewidth_diagnostics = []
    for gamma in WIDTHS:
        jets = scaled_lorentz_jets(t_grid, v_grid, gamma)
        jet_errors = {key: float(np.max(np.abs(jets[key] - limit_jets[key]))) for key in jets}
        omega_scaled = OMEGA_C + gamma * t_grid / 2.0
        # Independent evaluation of the manuscript's unfactored formula.
        direct = ((RHO * gamma * OMEGA_C)
                  / ((OMEGA_C**2 - gamma * OMEGA_C * v_grid)
                     - omega_scaled**2 - 1j * gamma * omega_scaled))
        convergence.append({
            "gamma": gamma,
            "max_absolute_errors_by_partial": jet_errors,
            "max_C2_error": max(jet_errors.values()),
            "direct_vs_scaled_formula_max_absolute_error": float(np.max(np.abs(direct - jets["value"]))),
        })
        v = centered_location(s_reference, gamma)
        notch_values = lorentz(omega_grid, gamma, v)
        linewidth_diagnostics.append({
            "gamma": gamma,
            "centered_v": v,
            "center_material_identity_absolute_error": float(abs(lorentz(OMEGA_C, gamma, v) - RHO * ell(v))),
            "resonance_frequency_squared": OMEGA_C**2 - gamma * OMEGA_C * v,
            "positive_residue": RHO * gamma * OMEGA_C,
            "minimum_sampled_imaginary_susceptibility_on_band": float(np.min(np.imag(notch_values))),
            "maximum_sampled_modulus_over_rho": float(np.max(np.abs(notch_values)) / RHO),
            "center_frequency_derivative_residual": abs(float(normalized_spectrum(OMEGA_C, s_reference, gamma, v, 1))),
            "scaled_center_derivative_residual": abs(float((gamma / 2.0) * normalized_spectrum(OMEGA_C, s_reference, gamma, v, 1))),
            "center_curvature": float(normalized_spectrum(OMEGA_C, s_reference, gamma, v, 2)),
            "sampled_global_check": sampled_global_check(s_reference, gamma, v),
        })

    def center_cross_section(s):
        v = centered_location(s, SELECTED_WIDTH)
        return s * s * float(normalized_spectrum(OMEGA_C, s, SELECTED_WIDTH, v))

    s_star = bisect(lambda s: center_cross_section(s) - TARGET, S_MINUS, S_PLUS)
    v_star = centered_location(s_star, SELECTED_WIDTH)
    s_grid = np.linspace(S_MINUS, S_PLUS, 13)
    bracket_checks = []
    for s in s_grid:
        v = centered_location(float(s), SELECTED_WIDTH)
        bracket_checks.append({
            "s": float(s), "v": v,
            "center_cross_section": center_cross_section(float(s)),
            "center_derivative_residual": abs(float(normalized_spectrum(OMEGA_C, s, SELECTED_WIDTH, v, 1))),
            "center_curvature": float(normalized_spectrum(OMEGA_C, s, SELECTED_WIDTH, v, 2)),
            "sampled_global_check": sampled_global_check(float(s), SELECTED_WIDTH, v),
        })

    # Independent two-variable finite differences of the final two equations.
    def equations(s, v):
        return np.array([
            s * s * float(normalized_spectrum(OMEGA_C, s, SELECTED_WIDTH, v)) - TARGET,
            (SELECTED_WIDTH / 2.0) * float(normalized_spectrum(OMEGA_C, s, SELECTED_WIDTH, v, 1)),
        ])

    step = 1.0e-5
    jacobian = np.column_stack(((equations(s_star + step, v_star) - equations(s_star - step, v_star)) / (2.0 * step),
                                (equations(s_star, v_star + step) - equations(s_star, v_star - step)) / (2.0 * step)))
    final = {
        "target_cross_section": TARGET,
        "selected_gamma": SELECTED_WIDTH,
        "s_bracket": [S_MINUS, S_PLUS],
        "endpoint_center_cross_sections": [center_cross_section(S_MINUS), center_cross_section(S_PLUS)],
        "selected_s": s_star, "selected_v": v_star,
        "center_cross_section": center_cross_section(s_star),
        "cross_section_target_absolute_residual": abs(center_cross_section(s_star) - TARGET),
        "center_cross_section_derivative_absolute_residual": s_star**2 * abs(float(normalized_spectrum(OMEGA_C, s_star, SELECTED_WIDTH, v_star, 1))),
        "center_cross_section_curvature": s_star**2 * float(normalized_spectrum(OMEGA_C, s_star, SELECTED_WIDTH, v_star, 2)),
        "equation_jacobian_finite_difference": jacobian.tolist(),
        "equation_jacobian_determinant": float(np.linalg.det(jacobian)),
        "jacobian_finite_difference_step": step,
        "sampled_global_check": sampled_global_check(s_star, SELECTED_WIDTH, v_star),
    }

    script_path = Path(__file__).resolve()
    manuscript_path = script_path.with_name("main.tex")
    results = {
        "diagnostic_kind": "ANALYTIC SURROGATE; NOT A MAXWELL OR DEVICE SIMULATION",
        "scope": [
            "Checks Fano algebra and curvature, Lorentz parametrization and sampled positive loss, scaled C2 convergence, center-slope roots, amplitude IVT, and dense sampled minima.",
            "The holomorphic nonlinear work response is an explicit surrogate and is not asserted to satisfy all Maxwell realizability constraints.",
            "No dielectric device dimensions, material caps, scattering, absorption, or asymmetry ratio are computed.",
            "Dense-grid minima and finite numerical residuals do not certify a continuum-band inequality or the manuscript theorem.",
        ],
        "source_sha256": hashlib.sha256(script_path.read_bytes()).hexdigest(),
        "manuscript_sha256_at_run": hashlib.sha256(manuscript_path.read_bytes()).hexdigest() if manuscript_path.exists() else None,
        "numpy_version": np.__version__,
        "model": {
            "kind": "Explicit analytic surrogate, not a Maxwell response",
            "normalized_extinction": "Y(omega,s,zeta)=baseline(omega,s)+Im[(A(s)+i B(s))*zeta+(0.15-0.10i)*zeta^2]",
            "cross_section_surrogate": "X=s^2*Y",
            "baseline": "1+0.08*x^2+6e-5*sin(900*x+phase1(s))+3e-5*cos(1370*x+phase2(s)); x=omega-1.5",
            "phase1": "0.90+0.40*(s-s_mid)",
            "phase2": "-0.35+0.20*(s-s_mid)",
            "A": "0.25+0.015*(s-s_mid)",
            "B": "0.80+0.010*(s-s_mid)",
            "s_mid": S_MID,
            "notch": "zeta=rho*gamma*omega_c/(Omega_v^2-omega^2-i*gamma*omega); Omega_v^2=omega_c^2-gamma*omega_c*v",
            "passivity_scope": "The added scalar Lorentz oscillator has positive residue and damping. No passivity or Maxwell realizability assertion is made for the surrogate work function itself.",
            "ordering": "The baseline ripples and work coefficients are fixed before the linewidth is narrowed.",
        },
        "parameters": {
            "band": list(BAND), "center_frequency": OMEGA_C, "rho": RHO,
            "bowl_coefficient": BOWL_K, "ripple_amplitudes": list(RIPPLE_AMPLITUDES),
            "ripple_frequencies": list(RIPPLE_FREQUENCIES),
            "rigorous_algebraic_baseline_lower_bound": Y_C - sum(RIPPLE_AMPLITUDES),
            "quadratic_work_coefficient": [QUADRATIC_WORK.real, QUADRATIC_WORK.imag],
            "root_bracket_tolerance": ROOT_TOLERANCE,
            "frequency_grid_count": FREQUENCY_GRID_COUNT,
            "inner_grid_count": INNER_GRID_COUNT,
            "inner_grid_half_width_in_t": INNER_GRID_HALF_WIDTH,
            "C2_error_grid_t_interval": [-4.0, 4.0],
            "C2_error_grid_t_count": 121,
            "C2_error_grid_v_interval": [u_nonlinear - 0.6, u_nonlinear + 0.6],
            "C2_error_grid_v_count": 91,
            "C2_error_scope": "Maximum sampled absolute error over all partial derivatives of total order at most two; not an interval bound.",
        },
        "fano_algebra": fano,
        "scaled_C2_convergence": convergence,
        "fixed_ripple_linewidth_diagnostics": linewidth_diagnostics,
        "positive_amplitude_bracket_samples": bracket_checks,
        "two_parameter_selection": final,
    }
    results["numerical_consistency_checks"] = {
        "fano_golden_location_matches_within_1e-6": fano["location_absolute_difference"] < 1.0e-6,
        "fano_curvature_formula_matches_differentiation_within_1e-12": abs(fano["leading_curvature_formula"] - fano["leading_curvature_differentiated"]) < 1.0e-12,
        "scaled_C2_errors_decrease_at_each_width": all(convergence[index + 1]["max_C2_error"] < convergence[index]["max_C2_error"] for index in range(len(convergence) - 1)),
        "all_sampled_Lorentz_imaginary_parts_positive": all(record["minimum_sampled_imaginary_susceptibility_on_band"] > 0.0 for record in linewidth_diagnostics),
        "broadest_stationary_center_fails_sampled_minimum": not linewidth_diagnostics[0]["sampled_global_check"]["center_is_sampled_minimum_to_2e-12"],
        "all_13_selected_width_bracket_samples_pass_sampled_minimum": all(record["sampled_global_check"]["center_is_sampled_minimum_to_2e-12"] for record in bracket_checks),
        "amplitude_endpoints_straddle_target": final["endpoint_center_cross_sections"][0] < TARGET < final["endpoint_center_cross_sections"][1],
        "final_target_residual_below_1e-10": final["cross_section_target_absolute_residual"] < 1.0e-10,
        "final_derivative_residual_below_1e-6": final["center_cross_section_derivative_absolute_residual"] < 1.0e-6,
        "final_center_curvature_positive": final["center_cross_section_curvature"] > 0.0,
        "final_jacobian_determinant_positive": final["equation_jacobian_determinant"] > 0.0,
        "final_center_passes_sampled_minimum": final["sampled_global_check"]["center_is_sampled_minimum_to_2e-12"],
    }
    if not all(results["numerical_consistency_checks"].values()):
        raise AssertionError(results["numerical_consistency_checks"])
    destination = script_path.with_name("numerical_results.json")
    destination.write_text(json.dumps(results, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "output": str(destination),
        "kind": results["diagnostic_kind"],
        "fano_depth": fano["nonlinear_frozen_minimum_depth"],
        "C2_errors": [[r["gamma"], r["max_C2_error"]] for r in convergence],
        "linewidth_center_is_sampled_minimum": [[r["gamma"], r["sampled_global_check"]["center_is_sampled_minimum_to_2e-12"]] for r in linewidth_diagnostics],
        "final_selection": final,
    }, indent=2))


if __name__ == "__main__":
    main()
