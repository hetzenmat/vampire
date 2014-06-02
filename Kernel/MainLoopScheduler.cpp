/**
 * @file MainLoopScheduler.cpp
 *
 * @date 7 May 2014
 * @author dmitry
 */

#include "Kernel/MainLoopScheduler.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/MainLoopContext.hpp"

#include "Lib/Allocator.hpp"

//#include "InstGen/IGAlgorithm.hpp"

//#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/SaturationAlgorithmContext.hpp"

//#include "Tabulation/TabulationAlgorithm.hpp"

//#include "Shell/BFNTMainLoop.hpp"
#include "Shell/Options.hpp"

namespace Kernel {

using Shell::Options;
//using namespace InstGen;
using Saturation::SaturationAlgorithmContext;
//using namespace Tabulation;

MainLoopScheduler::MainLoopScheduler(Problem& prb, OptionsList& opts) {

	  CALL("MainLoopScheduler::MainLoopScheduler");
	  _mlclSize = opts.size();

	  ASS_G(_mlclSize, 0);
	  //void* mem = ALLOC_KNOWN(_mlclSize*sizeof(MainLoopContext),"MainLoopScheduler");
	  //_mlcl = array_new<MainLoopContext>(mem,_mlclSize);

	  _mlcl = static_cast<MainLoopContext**>(
	  		  ALLOC_KNOWN(sizeof(MainLoopContext*)*_mlclSize,"MainLoopContext*"));

	  OptionsList::Iterator i(opts);
	  unsigned int k = 0;
	  while(i.hasNext()){

		  Options& opt = i.next();

		  /*if(opt.bfnt()) {
			_mla[k] = new BFNTMainLoop(prb, opt);
		  }

		  switch (opt.saturationAlgorithm()) {
		  case Options::TABULATION:
			_mla[k] = new TabulationAlgorithm(prb, opt);
			break;
		  case Options::INST_GEN:
			_mla[k] = new IGAlgorithm(prb, opt);
			break;
		  default:*/
			_mlcl[k] = new SaturationAlgorithmContext(prb, opt);


			/*break;
		  }*/

		  k++;
	  }
	  ASS_EQ(k, _mlclSize);
}

MainLoopResult MainLoopScheduler::run() {

	CALL("MainLoopScheduler::run");

	try {

		for(;;){
			for(unsigned int k = 0; k < _mlclSize; k++) {
				_mlcl[k] -> doStep();
/*				Timer::syncClock();
				if (env -> timeLimitReached()) {
					return MainLoopResult(Statistics::TIME_LIMIT);
				}
*/
			}
		}
		//Should never be here
	}catch(MainLoop::RefutationFoundException& rs) {
		return MainLoopResult(Statistics::REFUTATION, rs.refutation);
	}
	catch(TimeLimitExceededException&) {//We catch this since SaturationAlgorithm::doUnproceessedLoop throws it
		return MainLoopResult(Statistics::TIME_LIMIT);
	}
	catch(MainLoop::MainLoopFinishedException& e) {
		return e.result;
	}
}

MainLoopScheduler::~MainLoopScheduler() {

	CALL("MainLoopScheduler::~MainLoopScheduler()");

	for(unsigned int k = 0; k < _mlclSize; k++) {
		delete _mlcl[k]; //TODO: should be DEALLOC_UNKNOWN but SaturationAlgorithm::createFromOptions allocates via "new"
	}
	DEALLOC_KNOWN(_mlcl, sizeof(MainLoopContext*)*_mlclSize, "MainLoopScheduler");
}

/*static MainLoopScheduler* MainLoopScheduler::createFromOptions(Problem& prb, OptionsList* opts) {

	CALL("MainLoopScheduler::createFromOptions");
	return new MainLoopScheduler(prb, opts);

}*/
}
