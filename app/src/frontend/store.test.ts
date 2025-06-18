import { expect, test } from 'vitest'
import { setupStore, type AppStore } from './store'

test('setupStore returns an AppStore', () => {
    const store: AppStore = setupStore()
    expect(store).toBeDefined()
    expect(store.getState).toBeDefined()
    expect(store.dispatch).toBeDefined()
    expect(store.subscribe).toBeDefined()
    expect(store.replaceReducer).toBeDefined()
})
