// NAME: Guard actions possible
// RESULT: ACCEPT

// DESCRIPTION: 
region R(r) {
  guards |G|;
  interpretation {
    0 : true;
  }
  actions {
    G|1| : 1 ~> 2;
  }
}

