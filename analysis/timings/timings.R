library(tidyverse)

data <- read_csv("timings.csv")

grouped <- data %>% pivot_longer(init:ver, names_to = "phase", values_to = "time")
grouped$swaps <- as.factor(grouped$swaps)
subbed <- grouped %>%
  mutate(work_type = ifelse(phase == "pcrypto", "crypto", ifelse(phase == "psynth", "synth", "all"))) %>%
  mutate(phase = ifelse(work_type == "all", phase, "prover")) %>%
  arrange(work_type) %>% filter(phase != "init")
subbed$work_type <- factor(subbed$work_type, levels = c('all','synth', 'crypto'))

set_labels <- c(merkle = "Merkle", rsa = "RSA")
phase_labels <- c(param = "KeyGen", prover = "Proving", ver = "Verification")

ggplot(data = subbed, mapping = aes(y=time, x=swaps, fill = work_type)) +
  facet_grid(phase~set, scales="free_y", labeller = labeller(set = set_labels, phase = phase_labels)) +
  geom_col(position = "stack", color = "black") +
  guides(fill = guide_legend(reverse=TRUE)) +
  theme_light() +
  scale_fill_discrete(
    breaks = c("all", "synth", "crypto"),
    labels = c("All", "Synthesis", "Crypto.")
  ) +
  labs(
    fill = "Computation Type",
    y = "Time (s)",
    x = "Swaps",
    title = "Time Costs"
  ) +
  ggsave("timings.pdf", width = 6, height = 6, units = "in")
