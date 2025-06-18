import path from 'path';
import { app } from 'electron';
import Database from 'better-sqlite3';

let db: Database.Database | null = null;

export const openDatabase = () => {
    if (db) {
        return db;
    }

    const dbPath = path.join(app.getPath('userData'), 'db.sqlite');
    db = new Database(dbPath, {});
    db.pragma('journal_mode = WAL');
    return db;
}

export const closeDatabase = () => {
    if (db) {
        db.close();
        db = null;
    }
}
