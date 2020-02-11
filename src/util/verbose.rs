use std::env;

const VERBOSE_ENV_VAR: &str = "BELLMAN_BIGNAT_VERBOSE";

pub fn in_verbose_mode() -> bool {
    env::var(VERBOSE_ENV_VAR).is_ok()
}

pub fn set_verbose_mode(enable: bool) {
    if enable {
        env::set_var(VERBOSE_ENV_VAR, "1")
    } else if in_verbose_mode() {
        env::remove_var(VERBOSE_ENV_VAR)
    }
}
