# Copyright (c) 2021 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
# SPDX-License-Identifier: Apache-2.0

data "template_file" "vsts-agent-ubuntu_20_04-startup" {
  template = file("${path.module}/vsts_agent_ubuntu_20_04_startup.sh")

  vars = {
    vsts_token   = secret_resource.vsts-token.value
    vsts_account = "digitalasset"
    vsts_pool    = "ubuntu_20_04"
  }
}

resource "google_compute_region_instance_group_manager" "vsts-agent-ubuntu_20_04" {
  provider           = google-beta
  name               = "vsts-agent-ubuntu-20-04"
  base_instance_name = "vsts-agent-ubuntu-20-04"
  region             = "us-east1"
  target_size        = 20

  version {
    name              = "vsts-agent-ubuntu-20-04"
    instance_template = google_compute_instance_template.vsts-agent-ubuntu_20_04.self_link
  }

  update_policy {
    type            = "PROACTIVE"
    minimal_action  = "REPLACE"
    max_surge_fixed = 3
    min_ready_sec   = 60
  }
}

resource "google_compute_instance_template" "vsts-agent-ubuntu_20_04" {
  name_prefix  = "vsts-agent-ubuntu-20-04-"
  machine_type = "c2-standard-8"
  labels       = local.machine-labels

  disk {
    disk_size_gb = 200
    disk_type    = "pd-ssd"
    source_image = "ubuntu-os-cloud/ubuntu-2004-lts"
  }

  lifecycle {
    create_before_destroy = true
  }

  metadata = {
    startup-script = data.template_file.vsts-agent-ubuntu_20_04-startup.rendered

    shutdown-script = "#!/usr/bin/env bash\nset -euo pipefail\ncd /home/vsts/agent\nsu vsts <<SHUTDOWN_AGENT\nexport VSTS_AGENT_INPUT_TOKEN='${secret_resource.vsts-token.value}'\n./config.sh remove --unattended --auth PAT\nSHUTDOWN_AGENT\n    "
  }

  network_interface {
    network = "default"

    // Ephemeral IP to get access to the Internet
    access_config {}
  }

  service_account {
    email  = "log-writer@da-dev-gcp-daml-language.iam.gserviceaccount.com"
    scopes = ["cloud-platform"]
  }

  scheduling {
    automatic_restart   = false
    on_host_maintenance = "TERMINATE"
    preemptible         = false
  }
}
