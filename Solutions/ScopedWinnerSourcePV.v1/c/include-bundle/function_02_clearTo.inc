static void clearTo(unsigned int mark){if((mark>poolTop))fail();else ;
while((poolTop>mark)){(poolTop=(poolTop-1));
lean_dec((pool[poolTop]));}}
